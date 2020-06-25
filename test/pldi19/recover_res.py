#!/usr/bin/python3
TEX_FILE = "./results.tex"
with open(TEX_FILE) as f:
    dstrct = "TODO"
    # TODO: get data structure from \center{$STRUC}
    lines = f.read().splitlines()
    for l in lines:
        if(l[0] == '\\'):
            continue;
        else:
            clms = l.split("&").strip()
