"""Shared model loading and token statistics for the validation scripts."""
import os

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

NAME = os.environ.get("SEED_MODEL", "Qwen/Qwen3-8B-Base")
TAG = NAME.split("/")[-1].lower()
tok = AutoTokenizer.from_pretrained(NAME)
try:
    model = AutoModelForCausalLM.from_pretrained(NAME, dtype=torch.bfloat16)
except TypeError:
    model = AutoModelForCausalLM.from_pretrained(NAME, torch_dtype=torch.bfloat16)
model = model.cuda().eval()
BOS = tok.bos_token_id if tok.bos_token_id is not None else tok.eos_token_id

LAUGH_WORDS = [" haha", " hahaha", " lol", " LOL", " lmao", " Haha", " Hahaha", " ha", " Ha"]
LAUGH_IDS = sorted({tok.encode(w, add_special_tokens=False)[0] for w in LAUGH_WORDS
                    if len(tok.encode(w, add_special_tokens=False)) == 1})


@torch.no_grad()
def token_stats(context, text):
    """Per-token surprise, entropy (nats), rank, and the decoded tokens of text given context."""
    ctx = (tok(context, return_tensors="pt").input_ids if context
           else torch.tensor([[BOS]])).cuda()
    txt = tok(text, return_tensors="pt", add_special_tokens=False).input_ids.cuda()
    if txt.shape[1] == 0:
        z = torch.zeros(0, device="cuda")
        return z, z, z.long(), []
    logp = model(torch.cat([ctx, txt], 1)).logits[0, ctx.shape[1] - 1:-1]
    logp = logp.float().log_softmax(-1)
    chosen = logp.gather(1, txt[0][:, None])
    surprise = -chosen.squeeze(1)
    entropy = -(logp.exp() * logp).sum(-1)
    rank = (logp > chosen).sum(-1) + 1
    return surprise, entropy, rank, [tok.decode(t) for t in txt[0]]


@torch.no_grad()
def laugh_logp(text):
    """Log-probability that the next token after text is a laughter token."""
    ids = tok(text, return_tensors="pt").input_ids.cuda()
    logp = model(ids).logits[0, -1].float().log_softmax(-1)
    return torch.logsumexp(logp[LAUGH_IDS], 0).item()


def word_spans(tokens):
    spans, cur = [], []
    for i, t in enumerate(tokens):
        if cur and t[:1].isspace():
            spans.append(cur)
            cur = []
        cur.append(i)
    if cur:
        spans.append(cur)
    return spans
