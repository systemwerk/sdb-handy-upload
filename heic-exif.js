// =====================================================
// Schädiger-DB – HEIC-EXIF-Extraktion für die Handy-Upload-Seite
// Liest den EXIF-Block aus einem HEIC/HEIF-Container (ISO-BMFF) und
// liefert ihn als fertiges JPEG-APP1-Segment:
//   FF E1 | u16 Länge | "Exif\0\0" | TIFF   (TIFF ab Segment-Offset 10)
// Damit funktionieren normalizeExifOrientation, withExifSegment und
// parseExif aus index.html unverändert weiter.
// Jeder Fehler führt zu null — die Übertragung läuft dann ohne EXIF.
// =====================================================

(function() {
  'use strict';

  var META_SCAN_BYTES = 512 * 1024;
  var MAX_EXIF_BYTES = 256 * 1024;

  function isHeicFile(file) {
    return /^image\/hei[cf]$/i.test(file.type || '') || /\.hei[cf]$/i.test(file.name || '');
  }

  function boxType(view, pos) {
    return String.fromCharCode(view.getUint8(pos), view.getUint8(pos + 1),
      view.getUint8(pos + 2), view.getUint8(pos + 3));
  }

  // Iteriert über die Boxen in [pos, end); callback kann mit false abbrechen.
  // size==1 → 64-Bit-Größe (obere 32 Bit müssen 0 sein), size==0 → bis Ende.
  function eachBox(view, pos, end, callback) {
    while (pos + 8 <= end) {
      var size = view.getUint32(pos);
      var header = 8;
      if (size === 1) {
        if (pos + 16 > end || view.getUint32(pos + 8) !== 0) return;
        size = view.getUint32(pos + 12);
        header = 16;
      } else if (size === 0) {
        size = end - pos;
      }
      if (size < header) return;
      var boxEnd = Math.min(pos + size, end);
      if (callback(boxType(view, pos + 4), pos + header, boxEnd) === false) return;
      pos += size;
    }
  }

  function findBox(view, pos, end, wanted) {
    var found = null;
    eachBox(view, pos, end, function(type, start, boxEnd) {
      if (type === wanted) {
        found = { start: start, end: boxEnd };
        return false;
      }
    });
    return found;
  }

  // Sucht in iinf die item_ID des Items mit item_type "Exif".
  function findExifItemId(view, iinf) {
    var version = view.getUint8(iinf.start);
    var pos = iinf.start + 4 + (version === 0 ? 2 : 4); // version/flags + entry_count
    var exifId = null;
    eachBox(view, pos, iinf.end, function(type, start, boxEnd) {
      // Minimal-infe (v2): version/flags(4) + item_ID(2) + protection(2) + item_type(4) = 12
      if (type !== 'infe' || boxEnd - start < 12) return;
      var infeVersion = view.getUint8(start);
      if (infeVersion < 2) return;
      var itemId = infeVersion === 2 ? view.getUint16(start + 4) : view.getUint32(start + 4);
      var typePos = start + (infeVersion === 2 ? 8 : 10);
      if (typePos + 4 <= boxEnd && boxType(view, typePos) === 'Exif') {
        exifId = itemId;
        return false;
      }
    });
    return exifId;
  }

  // Liest aus iloc die Extents des Items als absolute Datei-Offsets.
  // Nur construction_method 0 (Datei-Offset); idat wird nicht unterstützt.
  function findItemExtents(view, iloc, itemId) {
    try {
      var version = view.getUint8(iloc.start);
      if (version > 2) return null;
      var pos = iloc.start + 4;
      var sizes = view.getUint16(pos); pos += 2;
      var offsetSize = (sizes >> 12) & 15;
      var lengthSize = (sizes >> 8) & 15;
      var baseOffsetSize = (sizes >> 4) & 15;
      var indexSize = version === 0 ? 0 : (sizes & 15);
      var itemCount;
      if (version < 2) { itemCount = view.getUint16(pos); pos += 2; }
      else { itemCount = view.getUint32(pos); pos += 4; }

      var readSized = function(size) {
        var value = 0;
        for (var i = 0; i < size; i++) value = value * 256 + view.getUint8(pos++);
        return value; // sicher bis 2^53 – weit über jeder Fotogröße
      };

      for (var i = 0; i < itemCount; i++) {
        var id;
        if (version < 2) { id = view.getUint16(pos); pos += 2; }
        else { id = view.getUint32(pos); pos += 4; }
        var constructionMethod = 0;
        if (version >= 1) { constructionMethod = view.getUint16(pos) & 15; pos += 2; }
        pos += 2; // data_reference_index
        var baseOffset = readSized(baseOffsetSize);
        var extentCount = view.getUint16(pos); pos += 2;
        var extents = [];
        for (var j = 0; j < extentCount; j++) {
          if (indexSize) readSized(indexSize);
          var extentOffset = readSized(offsetSize);
          var extentLength = readSized(lengthSize);
          extents.push({ offset: baseOffset + extentOffset, length: extentLength });
        }
        if (id === itemId) {
          return constructionMethod === 0 && extents.length ? extents : null;
        }
      }
    } catch (error) {
      // Ungültige iloc-Struktur → kein EXIF.
    }
    return null;
  }

  function isTiffHeader(view, pos) {
    if (pos < 0 || pos + 4 > view.byteLength) return false;
    var order = view.getUint16(pos);
    if (order !== 0x4949 && order !== 0x4D4D) return false;
    return view.getUint16(pos + 2, order === 0x4949) === 42;
  }

  // Exif-Payload nach ISO 23008-12: u32 exif_tiff_header_offset + Exif-Daten.
  function buildApp1(payload) {
    if (payload.length < 12) return null;
    var view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
    var tiffStart = 4 + view.getUint32(0);
    if (!isTiffHeader(view, tiffStart)) {
      tiffStart = -1;
      var scanEnd = Math.min(payload.length - 4, 68);
      for (var i = 4; i < scanEnd; i++) {
        if (isTiffHeader(view, i)) { tiffStart = i; break; }
      }
      if (tiffStart < 0) return null;
    }
    var tiff = payload.slice(tiffStart);
    var body = new Uint8Array(6 + tiff.length); // "Exif\0\0" + TIFF
    body.set([0x45, 0x78, 0x69, 0x66, 0, 0], 0);
    body.set(tiff, 6);
    if (body.length + 2 > 0xFFFF) return null; // passt nicht in ein APP1-Segment
    var segment = new Uint8Array(4 + body.length);
    segment[0] = 0xFF;
    segment[1] = 0xE1;
    segment[2] = (body.length + 2) >> 8;
    segment[3] = (body.length + 2) & 0xFF;
    segment.set(body, 4);
    return segment;
  }

  function extractAppSegment(file) {
    return file.slice(0, META_SCAN_BYTES).arrayBuffer().then(function(buffer) {
      var view = new DataView(buffer);
      if (buffer.byteLength < 16 || boxType(view, 4) !== 'ftyp') return null;
      var meta = findBox(view, 0, buffer.byteLength, 'meta');
      if (!meta) return null;
      var contentStart = meta.start + 4; // FullBox: version/flags überspringen
      var iinf = findBox(view, contentStart, meta.end, 'iinf');
      var iloc = findBox(view, contentStart, meta.end, 'iloc');
      if (!iinf || !iloc) return null;
      var itemId = findExifItemId(view, iinf);
      if (itemId === null) return null;
      var extents = findItemExtents(view, iloc, itemId);
      if (!extents) return null;
      var total = 0;
      extents.forEach(function(extent) { total += extent.length; });
      if (total < 12 || total > MAX_EXIF_BYTES) return null;
      return Promise.all(extents.map(function(extent) {
        return file.slice(extent.offset, extent.offset + extent.length).arrayBuffer();
      })).then(function(parts) {
        var payload = new Uint8Array(total);
        var write = 0;
        parts.forEach(function(part) {
          payload.set(new Uint8Array(part), write);
          write += part.byteLength;
        });
        return buildApp1(payload);
      });
    }).catch(function() { return null; });
  }

  window.sdbHeicExif = {
    isHeicFile: isHeicFile,
    extractAppSegment: extractAppSegment
  };
})();
