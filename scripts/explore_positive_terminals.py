#!/usr/bin/env python3
"""Untrusted bounded positive-terminal search and genuine word certificates."""
import json
from collections import deque
from pathlib import Path

MOVES = ("m1", "i1", "m2", "i2", "m3", "i3")
INVERSE = {"m1": "i1", "i1": "m1", "m2": "i2", "i2": "m2",
           "m3": "i3", "i3": "m3", **{f"s{i}": f"s{i}" for i in range(1, 5)}}
REPS = [(4,10,20,4,10,4), (5,14,40,5,16,4), (5,7,25,5,22,5),
        (7,8,18,4,13,4), (-6,-7,-3,3,7,6)]
SEED_WORDS = [["i1", "m3"], ["i1", "m3"], ["m3"], ["m3", "m2"], ["s1"]]

def step(z, g):
    a,b,c,d,e,f = z
    return {"m1": (a,a*b-d,a*c-e,b,c,f), "i1": (a,d,e,a*d-b,a*e-c,f),
            "m2": (a*d-b,a,c,d,d*e-f,e), "i2": (b,b*d-a,c,d,f,d*f-e),
            "m3": (a,f*b-c,b,f*d-e,d,f), "i3": (a,c,f*c-b,e,f*e-d,f),
            "s1": (-a,-b,-c,d,e,f), "s2": (-a,b,c,-d,-e,f),
            "s3": (a,-b,c,-d,e,-f), "s4": (a,b,-c,d,-e,-f)}[g]

def apply_word(z, w):
    for g in w:
        z = step(z, g)
    return z

def canonical(z):
    w = []
    for i,g in enumerate(("s2", "s3", "s4")):
        if z[i] < 0:
            z = step(z, g)
            w.append(g)
    return z,w

def candidates(bound, n=6, prefix=()):
    if n == 0:
        yield prefix
    else:
        for a in range(3, bound-3*(n-1)+1):
            yield from candidates(bound-a, n-1, prefix+(a,))

def solution_positive(z):
    a,b,c,d,e,f = z
    q1 = a*c*d*f-a*b*d-a*c*e-b*c*f-d*e*f+sum(t*t for t in z)
    q2 = a*f-b*e+c*d
    marker = 32+2*(a*b*d+a*c*e+b*c*f+d*e*f)-4*sum(t*t for t in z)
    return q1 == 8 and q2*q2 == 16 and marker > 0

def main():
    sols = [z for z in candidates(37) if solution_positive(z)]
    found = {}
    for i,(rep,seedword) in enumerate(zip(REPS, SEED_WORDS)):
        seed = apply_word(rep,seedword)
        seen = {seed: seedword}
        front = deque([seed])
        while front:
            z = front.popleft()
            for g in MOVES:
                nxt,signs = canonical(step(z,g))
                if sum(map(abs,nxt)) <= 75 and nxt not in seen:
                    seen[nxt] = seen[z]+[g]+signs
                    front.append(nxt)
        for z in sols:
            if z in seen:
                assert z not in found
                word = [INVERSE[g] for g in reversed(seen[z])]
                assert apply_word(z,word) == rep
                found[z] = {"tuple": z, "representative": i, "word_to_representative": word}
    assert len(sols) == len(found) == 23
    out = Path(__file__).with_name("positive_terminal_certificates.json")
    out.write_text(json.dumps([found[z] for z in sols], indent=2)+"\n")
    print(out)
    print("23 verified search certificates; class counts:",
          [sum(row["representative"] == i for row in found.values()) for i in range(5)])

if __name__ == "__main__":
    main()
