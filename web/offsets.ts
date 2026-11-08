// goat_web reports positions as UTF-8 byte offsets; editors index UTF-16 code
// units. The returned function converts the former to the latter for `source`,
// clamping offsets past the end to the end.
export function utf16Offsets(source: string): (byteOffset: number) => number {
  const toIndex: number[] = [];
  let index = 0;
  for (const char of source) {
    const code = char.codePointAt(0)!;
    const bytes = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;
    for (let i = 0; i < bytes; i++) toIndex.push(index);
    index += char.length;
  }
  toIndex.push(index);
  return (byteOffset) => toIndex[Math.min(byteOffset, toIndex.length - 1)];
}
