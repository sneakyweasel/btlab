export function Disclaimer({ children }: { children: string }) {
  return (
    <p className="rounded-md border border-line bg-card px-3 py-2 text-sm text-muted">
      {children}
    </p>
  );
}

export function Banner() {
  return (
    <p className="border-b border-line bg-deep px-4 py-2 text-center text-sm text-card">
      Period lower bounds at a verified descent floor. Not a halt theorem.
      Hitting 1 on one walk is not a proof that every start does.
    </p>
  );
}
