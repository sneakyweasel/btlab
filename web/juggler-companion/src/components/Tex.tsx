import katex from "katex";

type TexProps = {
  children: string;
  display?: boolean;
};

export function Tex({ children, display = false }: TexProps) {
  const html = katex.renderToString(children, {
    throwOnError: false,
    displayMode: display,
  });
  return (
    <span
      className={display ? "my-3 block overflow-x-auto" : ""}
      dangerouslySetInnerHTML={{ __html: html }}
    />
  );
}
