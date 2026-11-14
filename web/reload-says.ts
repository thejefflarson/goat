// What the editor says when a live edit reloads (ADR 0035): the copy table is part of
// the contract, so a kid is told which of their changes made the sketch start over.

import type { Reloaded } from "./loop.ts";

const RESHAPED = "Your sketch started over because your change reshaped what it remembers.";

// A reason that lacks the names its sentence needs falls back to `RESHAPED`
// rather than naming `undefined`.
export function reloadSays({ outcome, reason }: Reloaded): string {
  if (outcome === "refreshed") return "Updated: the ball kept going with your new `update`.";
  const [first, second, third] = reason?.args ?? [];
  switch (reason?.kind) {
    case "binding_gone":
      if (first) return `Your sketch started over because \`${first}\` is gone, and the ball's methods came from \`${first}\`.`;
      break;
    case "field_added":
      if (first) return `Your sketch started over because you added \`${first}\` to what it remembers.`;
      break;
    case "field_removed":
      if (first) return `Your sketch started over because it no longer remembers \`${first}\`.`;
      break;
    case "type_changed":
      if (first && second && third) {
        return `Your sketch started over because \`${first}\` changed from a \`${second}\` to a \`${third}\`.`;
      }
      break;
    case "method_added":
    case "method_lost":
      if (first) return `Your sketch started over because the ball got a new method, \`${first}\`.`;
      break;
    case "method_captures":
      if (first && second) {
        return `Your sketch started over because \`${first}\` uses \`${second}\` from where the ball was made, and that can't carry over.`;
      }
      break;
  }
  return RESHAPED;
}
