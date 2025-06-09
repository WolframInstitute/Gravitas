Package["WolframInstitute`Gravitas`"]

PackageExport["ChristoffelSymbols"]



ChristoffelSymbols[g_ ? IndexTensorQ] /; g["MetricQ"] := Block[{a, b, i, m, k, l, pd},
    pd = D[g[-a, -b], -i];
    IndexArray[1 / 2 IndexContract[{g[i, m], pd[-m, -k, -l] + pd[-m, -l, -k] - pd[-k, -l, -m]}], "\[CapitalGamma]"]
]

ChristoffelSymbols[mt_ ? MetricTensorQ] := ChristoffelSymbols[mt["IndexTensor"]]

