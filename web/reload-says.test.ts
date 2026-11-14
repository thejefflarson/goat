import assert from "node:assert/strict";
import test from "node:test";
import { reloadSays } from "./reload-says.ts";

const reset = (kind: string, ...args: string[]) => reloadSays({ outcome: "reset", reason: { kind, args } });

test("a refresh says the ball kept going", () => {
  assert.equal(reloadSays({ outcome: "refreshed" }), "Updated: the ball kept going with your new `update`.");
});

test("each reason has the sentence the contract gives it", () => {
  assert.equal(
    reset("binding_gone", "init"),
    "Your sketch started over because `init` is gone, and the ball's methods came from `init`.",
  );
  assert.equal(
    reset("field_added", "spin"),
    "Your sketch started over because you added `spin` to what it remembers.",
  );
  assert.equal(reset("field_removed", "vy"), "Your sketch started over because it no longer remembers `vy`.");
  assert.equal(
    reset("type_changed", "x", "Number", "String"),
    "Your sketch started over because `x` changed from a `Number` to a `String`.",
  );
  assert.equal(
    reset("method_added", "grow"),
    "Your sketch started over because the ball got a new method, `grow`.",
  );
  assert.equal(
    reset("method_lost", "grow"),
    "Your sketch started over because the ball got a new method, `grow`.",
  );
  assert.equal(
    reset("method_captures", "update", "speed"),
    "Your sketch started over because `update` uses `speed` from where the ball was made, and that can't carry over.",
  );
});

test("a reshaped model, an ambiguous site, an unknown kind and a missing name all fall back", () => {
  const fallback = "Your sketch started over because your change reshaped what it remembers.";
  assert.equal(reset("reshaped"), fallback);
  assert.equal(reset("ambiguous_site", "update"), fallback);
  assert.equal(reset("something_new", "x"), fallback);
  assert.equal(reset("field_added"), fallback);
  assert.equal(reset("type_changed", "x", "Number"), fallback);
  assert.equal(reloadSays({ outcome: "reset" }), fallback);
});
