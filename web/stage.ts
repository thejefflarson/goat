// The page's drawing area for a supervised program. A canvas can hand its
// drawing to a worker only once (`transferControlToOffscreen`), and a terminated
// worker takes its surface with it, so every start gets a fresh canvas element
// swapped into the same place.

export class Stage {
  #template: HTMLCanvasElement;
  #current: HTMLCanvasElement;

  constructor(canvas: HTMLCanvasElement) {
    this.#template = canvas.cloneNode(false) as HTMLCanvasElement;
    this.#current = canvas;
  }

  get canvas(): HTMLCanvasElement {
    return this.#current;
  }

  // The element that holds the canvas; input listeners go here because they
  // must outlive any one canvas.
  get container(): HTMLElement {
    return this.#current.parentElement!;
  }

  surface(): OffscreenCanvas {
    const next = this.#template.cloneNode(false) as HTMLCanvasElement;
    this.#current.replaceWith(next);
    this.#current = next;
    return next.transferControlToOffscreen();
  }

  focus(): void {
    this.#current.focus();
  }
}
