Package["WolframInstitute`Gravitas`ShapedTensor`"]

PackageScope[tensorName]
PackageScope[tensorDimensions]
PackageScope[tensorRank]
PackageScope[setDimensions]



tensorDimensions[t_] := Replace[TensorDimensions[t], Except[_List] :> Dimensions[t]]

tensorRank[t_] := Replace[TensorRank[t], Except[_Integer] -> 0]


TensorSymbol = VectorSymbol | MatrixSymbol | ArraySymbol

TensorAssumptions = Vectors | Matrices | Arrays


tensorName[t_Symbol ? AtomQ] := t

tensorName[TensorSymbol[s_, ___]] := s

tensorName[___] := None


setDimensions[TensorSymbol[s_, _, dom_ : Reals, sym___], dims : {___Integer ? Positive}] := Switch[dims,
    {_}, VectorSymbol[s, dims, dom],
    {_, _}, MatrixSymbol[s, dims, dom, sym],
    _, ArraySymbol[s, dims, dom, sym]
]

setDimensions[s_Symbol ? AtomQ, dims : {___Integer ? Positive}] := With[{
    pos = FirstPosition[$Assumptions, Element[s, _], Missing[], {1}, Heads -> False],
    head = Switch[dims, {_}, Vectors, {_, _}, Matrices, {_, _, _}, Arrays]
},
    If[ MissingQ[pos],
        AppendTo[$Assumptions, Element[s, head[dims, Reals]]],
        $Assumptions //= ReplacePart[
            pos -> Replace[
                Extract[$Assumptions, pos],
                Element[_, TensorAssumptions[_, dom_ : Reals, sym___]] :> Element[s, head[dims, dom, sym]]
            ]
        ]
    ];
    s
]

setDimensions[t_, dims : {___, 0, ___}] := ArrayReshape[{}, Append[DeleteCases[dims, 0], 0]]

setDimensions[t_, dims : {___Integer ? Positive}, pad_ : 0] :=
    PadRight[
        Replace[
            ArrayDepth[t] - Length[dims],
            {
                0 :> t,
                p_Integer ? Positive :> Flatten[t, p],
                n_Integer :> Nest[List, t, - n]
            }
        ],
        dims,
        pad
    ]