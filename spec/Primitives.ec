op prf : seed -> adrs -> key.
op f : key -> nbytes -> nbytes.
op nbytexor(a b : nbytes) = 
    map (fun (ab : W8.t*W8.t) => ab.`1 `^` ab.`2) (zip a b).