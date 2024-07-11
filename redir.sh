#!/bin/sh

for f in smt/* pdf/* ; do
  cat <<EOF
{
    "route": "/$f",
    "redirect": "https://mmoskal.github.io/$f"
},
EOF
done
