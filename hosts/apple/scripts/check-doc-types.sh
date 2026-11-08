#!/bin/sh
# Checks that the generated Info.plists declare exactly the content type
# GoatDocument opens: the document type's LSItemContentTypes, the exported UTI,
# and UTType.goatSource must all name the same identifier. A mismatch makes the
# Files browser refuse to open or create .goat documents. Run after `xcodegen generate`.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
source="$here/GoatKit/Sources/GoatKit/GoatDocument.swift"

declared=$(sed -n 's/.*UTType(exportedAs: "\([^"]*\)".*/\1/p' "$source")
[ -n "$declared" ] || { echo "error: no UTType(exportedAs:) in $source" >&2; exit 1; }
grep -q 'readableContentTypes = \[UTType.goatSource\]' "$source" ||
  { echo "error: GoatDocument.readableContentTypes is not [UTType.goatSource]" >&2; exit 1; }

for plist in "$here/Info-macOS.plist" "$here/Info-iOS.plist"; do
  handled=$(plutil -extract CFBundleDocumentTypes.0.LSItemContentTypes.0 raw -o - "$plist")
  exported=$(plutil -extract UTExportedTypeDeclarations.0.UTTypeIdentifier raw -o - "$plist")
  ext=$(plutil -extract UTExportedTypeDeclarations.0.UTTypeTagSpecification.public\\.filename-extension.0 raw -o - "$plist")
  for found in "$handled" "$exported"; do
    [ "$found" = "$declared" ] ||
      { echo "error: $(basename "$plist") declares $found, GoatDocument uses $declared" >&2; exit 1; }
  done
  [ "$ext" = "goat" ] ||
    { echo "error: $(basename "$plist") maps extension '$ext', expected goat" >&2; exit 1; }
done
