"""Exact CPU trajectory census. Arbitrary-precision floor_power."""

from __future__ import annotations

from research.juggler_sequence.atlas.packed import dense_index, dense_size
from research.juggler_sequence.power_itineraries import floor_power


def census(
    *,
    k_max: int,
    n_max: int,
    n_begin: int = 1,
) -> tuple[list[int | None], list[int | None], list[int | None]]:
    """Return dense tables of min realizer, min expanding realizer, end state.

    End state is ``T^{length}(min_realizer)``. Starts run from ``n_begin``
    through ``n_max`` inclusive.
    """

    if k_max < 0 or n_max < 0 or n_begin < 1:
        raise ValueError("invalid census bounds")
    size = dense_size(k_max)
    min_n: list[int | None] = [None] * size
    min_exp: list[int | None] = [None] * size
    end_at_min: list[int | None] = [None] * size
    for n in range(n_begin, n_max + 1):
        state = n
        packed = 0
        for depth in range(1, k_max + 1):
            packed |= (state & 1) << (depth - 1)
            idx = dense_index(depth, packed)
            nxt = floor_power(state)
            if min_n[idx] is None or n < min_n[idx]:
                min_n[idx] = n
                end_at_min[idx] = nxt
            if n < nxt and (min_exp[idx] is None or n < min_exp[idx]):
                min_exp[idx] = n
            state = nxt
    return min_n, min_exp, end_at_min


def merge_starts(
    min_n: list[int | None],
    min_exp: list[int | None],
    starts: list[int],
    *,
    k_max: int,
) -> None:
    """Replay exact trajectories for starts the native kernel overflowed."""

    for n in starts:
        state = n
        packed = 0
        for depth in range(1, k_max + 1):
            packed |= (state & 1) << (depth - 1)
            idx = dense_index(depth, packed)
            nxt = floor_power(state)
            if min_n[idx] is None or n < min_n[idx]:
                min_n[idx] = n
            if n < nxt and (min_exp[idx] is None or n < min_exp[idx]):
                min_exp[idx] = n
            state = nxt


def fill_end_states(
    min_n: list[int | None],
    *,
    k_max: int,
    bit_limit: int = 128,
) -> list[int | None]:
    """Image of each min realizer. Skip ends that exceed ``bit_limit``."""

    ends: list[int | None] = [None] * len(min_n)
    for length in range(1, k_max + 1):
        for packed in range(1 << length):
            idx = dense_index(length, packed)
            n = min_n[idx]
            if n is None:
                continue
            state = n
            too_wide = False
            for _ in range(length):
                if state.bit_length() > bit_limit:
                    too_wide = True
                    break
                state = floor_power(state)
            ends[idx] = None if too_wide or state.bit_length() > bit_limit else state
    return ends


def iter_dense(
    k_max: int,
    min_n: list[int | None],
    min_exp: list[int | None],
    end_at_min: list[int | None],
):
    for length in range(1, k_max + 1):
        for packed in range(1 << length):
            idx = dense_index(length, packed)
            yield length, packed, min_n[idx], min_exp[idx], end_at_min[idx]
