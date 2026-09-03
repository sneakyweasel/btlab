export function Disclaimer({ children }: { children: string }) {
  return (
    <p className="rounded-md border border-line bg-card px-3 py-2 text-sm text-muted">
      {children}
    </p>
  );
}
