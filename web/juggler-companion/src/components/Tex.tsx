import katex from "katex";
import { memo, useMemo } from "react";

type TexProps = {
  children: string;
  display?: boolean;
};

export const Tex = memo(function Tex({ children, display = false }: TexProps) {
  const html = useMemo(
    () =>
      katex.renderToString(children, {
        throwOnError: false,
        displayMode: display,
      }),
    [children, display],
  );
  return (
    <span
      className={display ? "my-3 block overflow-x-auto" : ""}
      dangerouslySetInnerHTML={{ __html: html }}
    />
  );
});
