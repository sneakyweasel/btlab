import type { ReactNode } from "react";

function FrameIcon({
  children,
  large,
}: {
  children: ReactNode;
  large?: boolean;
}) {
  return (
    <svg
      viewBox="0 0 16 16"
      className={large ? "h-4 w-4" : "h-3.5 w-3.5"}
      fill="currentColor"
      aria-hidden
    >
      {children}
    </svg>
  );
}

function IconFirst() {
  return (
    <FrameIcon>
      <rect x="2" y="3" width="2" height="10" rx="0.4" />
      <path d="M14 3.2v9.6L6.2 8z" />
    </FrameIcon>
  );
}

function IconPrevFrame() {
  return (
    <FrameIcon>
      <path d="M12.4 3.2v9.6L4.2 8z" />
    </FrameIcon>
  );
}

function IconPlay() {
  return (
    <FrameIcon large>
      <path d="M4 2.8v10.4L13.6 8z" />
    </FrameIcon>
  );
}

function IconPause() {
  return (
    <FrameIcon large>
      <rect x="3.4" y="3" width="3" height="10" rx="0.5" />
      <rect x="9.6" y="3" width="3" height="10" rx="0.5" />
    </FrameIcon>
  );
}

function IconNextFrame() {
  return (
    <FrameIcon>
      <path d="M3.6 3.2v9.6L11.8 8z" />
    </FrameIcon>
  );
}

function IconLast() {
  return (
    <FrameIcon>
      <path d="M2 3.2v9.6L9.8 8z" />
      <rect x="12" y="3" width="2" height="10" rx="0.4" />
    </FrameIcon>
  );
}

function Transport({
  label,
  disabled,
  primary,
  onClick,
  children,
}: {
  label: string;
  disabled?: boolean;
  primary?: boolean;
  onClick: () => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      aria-label={label}
      title={label}
      disabled={disabled}
      onClick={onClick}
      className={
        primary
          ? "flex h-9 w-9 items-center justify-center rounded-full bg-deep text-card disabled:opacity-40"
          : "flex h-8 w-8 items-center justify-center rounded-full text-ink disabled:opacity-35 hover:bg-line/50"
      }
    >
      {children}
    </button>
  );
}

type MediaScrubberProps = {
  value: number;
  min: number;
  max: number;
  onSeek: (value: number) => void;
};

export function MediaScrubber({ value, min, max, onSeek }: MediaScrubberProps) {
  const span = Math.max(max - min, 0);
  const progressPct = span === 0 ? 0 : (100 * (value - min)) / span;
  return (
    <div className="relative flex h-4 items-center">
      <div className="pointer-events-none absolute inset-x-0 h-1 rounded-full bg-line" />
      <div
        className="pointer-events-none absolute left-0 h-1 rounded-full bg-deep"
        style={{ width: `${progressPct}%` }}
      />
      <input
        className="trajectory-scrubber relative z-10"
        type="range"
        min={min}
        max={max}
        step={1}
        value={value}
        aria-label="Frame"
        aria-valuemin={min}
        aria-valuemax={max}
        aria-valuenow={value}
        onChange={(event) => onSeek(Number(event.target.value))}
      />
    </div>
  );
}

type MediaPlayerProps = {
  playing: boolean;
  prevLabel?: string;
  nextLabel?: string;
  firstDisabled?: boolean;
  prevDisabled?: boolean;
  nextDisabled?: boolean;
  lastDisabled?: boolean;
  onFirst: () => void;
  onPrev: () => void;
  onPlay: () => void;
  onNext: () => void;
  onLast: () => void;
};

export function MediaPlayer({
  playing,
  prevLabel = "",
  nextLabel = "",
  firstDisabled,
  prevDisabled,
  nextDisabled,
  lastDisabled,
  onFirst,
  onPrev,
  onPlay,
  onNext,
  onLast,
}: MediaPlayerProps) {
  return (
    <div className="flex w-full items-center justify-center gap-3">
      <p className="min-w-0 flex-1 text-right font-mono text-sm leading-tight break-all text-muted">
        {prevLabel}
      </p>
      <div className="flex shrink-0 items-center gap-0.5">
        <Transport label="First frame" disabled={firstDisabled} onClick={onFirst}>
          <IconFirst />
        </Transport>
        <Transport
          label="Previous frame (←)"
          disabled={prevDisabled}
          onClick={onPrev}
        >
          <IconPrevFrame />
        </Transport>
        <Transport
          label={playing ? "Pause (space)" : "Play (space)"}
          primary
          onClick={onPlay}
        >
          {playing ? <IconPause /> : <IconPlay />}
        </Transport>
        <Transport label="Next frame (→)" disabled={nextDisabled} onClick={onNext}>
          <IconNextFrame />
        </Transport>
        <Transport label="Last frame" disabled={lastDisabled} onClick={onLast}>
          <IconLast />
        </Transport>
      </div>
      <p className="min-w-0 flex-1 font-mono text-sm leading-tight break-all text-muted">
        {nextLabel}
      </p>
    </div>
  );
}

type MediaControlsProps = {
  value: number;
  min: number;
  max: number;
  playing: boolean;
  loop?: boolean;
  prevLabel?: string;
  nextLabel?: string;
  onSeek: (value: number) => void;
  onPlay: () => void;
};

export function MediaControls({
  value,
  min,
  max,
  playing,
  loop = false,
  prevLabel,
  nextLabel,
  onSeek,
  onPlay,
}: MediaControlsProps) {
  const atMin = value <= min;
  const atMax = value >= max;
  return (
    <div className="space-y-2">
      <MediaScrubber value={value} min={min} max={max} onSeek={onSeek} />
      <MediaPlayer
        playing={playing}
        prevLabel={prevLabel}
        nextLabel={nextLabel}
        firstDisabled={!loop && atMin}
        prevDisabled={!loop && atMin}
        nextDisabled={!loop && atMax}
        lastDisabled={!loop && atMax}
        onFirst={() => onSeek(min)}
        onPrev={() => onSeek(loop && atMin ? max : value - 1)}
        onPlay={onPlay}
        onNext={() => onSeek(loop && atMax ? min : value + 1)}
        onLast={() => onSeek(max)}
      />
    </div>
  );
}
