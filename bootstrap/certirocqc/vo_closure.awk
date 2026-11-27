# The .vo files of the workspace that the given ones need, transitively, from the
# output of rocq dep, where the dependencies of a file are those of its .vo target (the
# installed ones, with absolute paths, are left out). The given files are included.
#
#   rocq dep ... | awk -f vo_closure.awk -v roots="a.vo b.vo"

$1 ~ /\.vo$/ {
    for (i = 2; i <= NF; i++)
        if ($i ~ /\.vo$/ && $i !~ /^\//)
            deps[$1] = deps[$1] " " $i
}

END {
    n = split(roots, todo, " ")
    while (n > 0) {
        f = todo[n--]
        if (f in seen)
            continue
        seen[f] = 1
        print f
        m = split(deps[f], fdeps, " ")
        for (j = 1; j <= m; j++)
            todo[++n] = fdeps[j]
    }
}
