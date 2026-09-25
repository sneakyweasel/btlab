import { useEffect, useRef, useState } from "react";

/** Width of a container element, tracked with ResizeObserver. */
export function useWidth<T extends HTMLElement>(initial = 720, minimum = 260) {
  const ref = useRef<T>(null);
  const [width, setWidth] = useState(initial);
  useEffect(() => {
    if (!ref.current) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(minimum, entry.contentRect.width)));
    observer.observe(ref.current);
    return () => observer.disconnect();
  }, [minimum]);
  return [ref, width] as const;
}
