import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { run } from "/Users/jeff/dev/goat/.claude/worktrees/agent-a12635fc60c5b0dc6/web/runtime.ts";

const goat = "/Users/jeff/dev/goat/.claude/worktrees/agent-a12635fc60c5b0dc6/target/release/goat";
const dir = "/private/tmp/claude-501/-Users-jeff-dev-goat/e79b6470-0795-449b-93bc-2c8f1143db7b/scratchpad";

const prelude = (n: number) => `
speed = 3
make = program(i) do
  {x: i, y: 0, vx: 1, vy: 2,
   update: program(self, dt) do {...self, x: self.x + self.vx * dt * speed} done,
   draw: program(self) do self.x * speed done}
done
build = program(i, acc) do if i == 0 then acc else build(i - 1, Link(make(i), acc)) done done
snap = program(xs) do match xs do
  Empty then Empty
  Link(b, rest) then Link({x: b.x, y: b.y, vx: b.vx, vy: b.vy}, snap(rest))
done done
refresh = program(xs) do match xs do
  Empty then Empty
  Link(d, rest) then Link({x: d.x, y: d.y, vx: d.vx, vy: d.vy,
    update: program(self, dt) do {...self, x: self.x + self.vx * dt * speed} done,
    draw: program(self) do self.x * speed done}, refresh(rest))
done done
step = program(xs) do match xs do
  Empty then Empty
  Link(b, rest) then Link(b.update(16), step(rest))
done done
total = program(xs) do match xs do
  Empty then 0
  Link(b, rest) then b.draw() + total(rest)
done done
old = build(${n}, Empty)
`;

const phases: Record<string, string> = {
  build: "print(total(old))",
  frame: "print(total(step(old)))",
  snapshot: "s = snap(old)\nprint(length(s))",
  snapshot_refresh: "s = snap(old)\nprint(total(refresh(s)))",
};

async function time(name: string, n: number, reps: number) {
  const src = prelude(n) + phases[name];
  const file = `${dir}/p_${name}_${n}.goat`;
  writeFileSync(file, src);
  const wasm = `${dir}/p_${name}_${n}.wasm`;
  execFileSync(goat, ["build", file, "-o", wasm]);
  const bytes = readFileSync(wasm);
  const module = await WebAssembly.compile(bytes);
  const samples: number[] = [];
  for (let i = 0; i < reps; i++) {
    const t = performance.now();
    await run(bytes);
    samples.push(performance.now() - t);
  }
  samples.sort((a, b) => a - b);
  return samples[Math.floor(samples.length / 2)]!;
}

for (const n of [100, 1000, 3000]) {
  const out: Record<string, number> = {};
  for (const name of Object.keys(phases)) out[name] = await time(name, n, 40);
  console.log(n, JSON.stringify(out));
}
