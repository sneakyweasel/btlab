import type { ReactNode } from "react";
import { Tex } from "./Tex";

const TOKEN =
  /(\$\$[\s\S]+?\$\$|\$[^$\n]+?\$|`[^`]+`|\*\*[^*]+?\*\*)/g;

function RichText({ text }: { text: string }) {
  const parts = text.split(TOKEN).filter((part) => part !== "");
  return (
    <>
      {parts.map((part, index) => {
        const key = `${index}:${part.slice(0, 12)}`;
        if (part.startsWith("$$") && part.endsWith("$$")) {
          return <Tex key={key} display>{part.slice(2, -2)}</Tex>;
        }
        if (part.startsWith("$") && part.endsWith("$")) {
          return <Tex key={key}>{part.slice(1, -1)}</Tex>;
        }
        if (part.startsWith("`") && part.endsWith("`")) {
          return (
            <code key={key} className="font-mono text-[0.92em] text-deep">
              {part.slice(1, -1)}
            </code>
          );
        }
        if (part.startsWith("**") && part.endsWith("**")) {
          return (
            <strong key={key} className="font-serif font-medium text-ink">
              {part.slice(2, -2)}
            </strong>
          );
        }
        return <span key={key}>{part}</span>;
      })}
    </>
  );
}

type ProseProps = {
  text: string;
  className?: string;
  muted?: boolean;
};

export function Prose({ text, className = "", muted = false }: ProseProps) {
  const paragraphs = text.split(/\n\n+/);
  return (
    <div className={`space-y-4 ${className}`.trim()}>
      {paragraphs.map((paragraph) => (
        <p
          key={paragraph.slice(0, 40)}
          className={`prose-measure ${muted ? "text-muted" : ""}`.trim()}
        >
          <RichText text={paragraph} />
        </p>
      ))}
    </div>
  );
}

export function ProseInline({ text }: { text: string }): ReactNode {
  return <RichText text={text} />;
}
