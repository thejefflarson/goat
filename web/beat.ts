// The page's half of the native host's watchdog (ADR 0021). A host that cannot
// run goat in a worker (the Apple app's WKWebView) keeps it on the page's thread,
// where nothing on the page can interrupt a spinning call. So the page tells the
// host when goat is entered and left; a call that never leaves is the host's cue
// to tear the web view down.
//
// The count is odd while goat runs and even while the page is idle, the same
// parity the worker supervisor reads from its shared word (protocol.ts). Only
// synchronous calls are bracketed, so they never nest or interleave and the
// parity stays true. The entering message is posted before the call runs, so a
// call that never returns has already told the host it started.

// Which deadline applies to the call: one frame's `setup`/`update`/`draw`, or a
// whole run-once program.
export type CallKind = "frame" | "once";

export interface BeatMessage {
  type: "beat";
  count: number;
  call: CallKind;
}

export interface Beat {
  around<T>(call: CallKind, work: () => T): T;
}

export function createBeat(post: (message: BeatMessage) => void): Beat {
  let count = 0;
  const mark = (call: CallKind) => post({ type: "beat", count: ++count, call });
  return {
    around(call, work) {
      mark(call);
      try {
        return work();
      } finally {
        mark(call);
      }
    },
  };
}
