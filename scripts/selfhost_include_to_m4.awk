#!/usr/bin/awk -f

match($0, /^[[:space:]]*\(\*[[:space:]]*\$I[[:space:]]+([^[:space:]]+)[[:space:]]*\*\)[[:space:]]*$/, m) {
    printf("include(`%s')dnl\n", m[1]);
    next;
}

{
    print;
}
