"""Rank statistics without scipy."""
import numpy as np


def rankdata(x):
    x = np.asarray(x, dtype=float)
    order = np.argsort(x)
    ranks = np.empty(len(x))
    ranks[order] = np.arange(1, len(x) + 1)
    # average ties
    _, inv, counts = np.unique(x, return_inverse=True, return_counts=True)
    sums = np.zeros(len(counts))
    np.add.at(sums, inv, ranks)
    return sums[inv] / counts[inv]


def spearman(a, b):
    ra, rb = rankdata(a), rankdata(b)
    ra, rb = ra - ra.mean(), rb - rb.mean()
    d = np.sqrt((ra ** 2).sum() * (rb ** 2).sum())
    return float((ra * rb).sum() / d) if d else 0.0


def auc(scores, labels):
    """Probability a random positive scores above a random negative."""
    scores, labels = np.asarray(scores, dtype=float), np.asarray(labels).astype(bool)
    n_pos, n_neg = labels.sum(), (~labels).sum()
    if n_pos == 0 or n_neg == 0:
        return float("nan")
    r = rankdata(scores)
    return float((r[labels].sum() - n_pos * (n_pos + 1) / 2) / (n_pos * n_neg))
