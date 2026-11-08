// Page-side input for a supervised program: DOM key and pointer events become
// host events and go to the worker by message. `events` must outlive the canvas,
// which the supervisor replaces on every start, so listeners sit on a container
// that the canvas's events bubble up to.

import {
  type DomEvent,
  KEY_EVENTS,
  type ListenerTarget,
  type LoopCanvas,
  POINTER_EVENTS,
  pointerPosition,
} from "./loop.ts";
import type { EventKind, HostEvent } from "./scene.ts";

export interface InputSink {
  wants(kind: EventKind): boolean;
  input(event: HostEvent): void;
}

export function forwardInput(
  events: ListenerTarget,
  canvas: () => Pick<LoopCanvas, "width" | "height" | "getBoundingClientRect">,
  to: InputSink,
): () => void {
  const removers: Array<() => void> = [];
  const listen = (type: string, listener: (event: DomEvent) => void) => {
    events.addEventListener(type, listener);
    removers.push(() => events.removeEventListener(type, listener));
  };
  for (const [type, kind] of Object.entries(KEY_EVENTS)) {
    listen(type, (e) => {
      if (typeof e.key !== "string" || !to.wants(kind)) return;
      e.preventDefault?.();
      to.input({ kind, key: e.key });
    });
  }
  for (const [type, kind] of Object.entries(POINTER_EVENTS)) {
    listen(type, (e) => {
      if (!to.wants(kind)) return;
      const at = pointerPosition(canvas(), e);
      if (at) to.input({ kind, ...at });
    });
  }
  return () => removers.forEach((remove) => remove());
}
