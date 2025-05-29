Package["WolframInstitute`Gravitas`IndexArray`TensorUtilities`"]

PackageExport[tensorDimensions]
PackageExport[tensorName]
PackageExport[tensorRank]
PackageExport[tensorPart]
PackageExport[tensorTranspose]

PackageExport[squareMatrixQ]

PackageExport[setDimensions]



ClearAll[tensorDimensions, tensorRank, tensorName, tensorPart, tensorTranspose, squareMatrixQ, setDimensions]


tensorDimensions[t_] := Replace[TensorDimensions[t], Except[_List] :> {}]

tensorRank[t_] := Replace[TensorRank[t], Except[_Integer] -> 0]


TensorSymbol = VectorSymbol | MatrixSymbol | ArraySymbol

TensorAssumptions = Vectors | Matrices | Arrays


tensorName[t_Symbol ? AtomQ] := t

tensorName[TensorSymbol[s_, ___]] := s

tensorName[___] := None

squareMatrixQ[t_] := MatchQ[tensorDimensions[t], {n_, n_} | {_, 0}]


setDimensions[TensorSymbol[s_, _, dom_ : Reals, sym_ : {}], dims : {___Integer ? Positive}] := Switch[dims,
    {_}, VectorSymbol[s, dims, dom],
    {_, _}, MatrixSymbol[s, dims, dom, sym],
    _, ArraySymbol[s, dims, dom, sym]
]

setDimensions[s_Symbol ? AtomQ, dims : {___Integer ? Positive}, defDom_ : Reals, defSym_ : {}] := Block[{
    pos,
    newElement = With[{head = Switch[dims, {_}, Vectors, {_, _}, Matrices, _, Arrays]},
        If[head === Vectors, Element[s, head[dims, #]] &,  Element[s, head[dims, ##]] &]
    ]
},
    $Assumptions = Developer`ToList[$Assumptions];
    pos = FirstPosition[$Assumptions, Element[s, _], Missing[], {1}, Heads -> False];
    If[ MissingQ[pos],
        AppendTo[$Assumptions, newElement[defDom, defSym]],
        $Assumptions //= ReplacePart[
            pos -> Replace[
                Extract[$Assumptions, pos],
                Element[_, TensorAssumptions[_, dom_ : defDom, sym_ : defSym]] :> newElement[dom, sym]
            ]
        ]
    ];
    s
]

setDimensions[t_, dims : {___, 0, ___}] := ArrayReshape[{}, Append[DeleteCases[dims, 0], 0]]

setDimensions[t_, dims : {___Integer ? Positive}, pad_ : 0] := With[{
    s = Replace[
        ArrayDepth[t] - Length[dims],
        {
            0 :> t,
            p_Integer ? Positive :> Flatten[t, p],
            n_Integer :> Nest[List, t, - n]
        }
    ]
},
    If[dims === {}, s, PadRight[s, dims, pad]]
]


tensorPart[t_, {i_, is___}, k_ : 0] := With[{nest = Nest[#[] &, #, k] &},
    If[ i === All,
        tensorPart[t, {is}, k + 1],
        tensorPart[
            Replace[
                t,
                {
                    (VectorSymbol | ArraySymbol)[s_, {_} | _Integer, dom___] /; k < 1 :> ArraySymbol[nest[s][i], {}, dom],
                    (MatrixSymbol | ArraySymbol)[s_, ds : {_, _}, dom_ : Reals, ___] /; k < 2 :> VectorSymbol[nest[s][i], Drop[ds, {k + 1}], dom],
                    HoldPattern[ArraySymbol[s_, ds_List, dom_, ___]] /; k < Length[ds] :> If[Length[ds] - k == 3, MatrixSymbol, ArraySymbol][nest[s][i], Drop[ds, {k + 1}], dom],
                    s_Symbol ? AtomQ :> setDimensions[s, Drop[tensorDimensions[t], {k + 1}]],
                    _ :> (Part[t, ##] & @@ Append[ConstantArray[All, k], i])
                }
            ],
            {is},
            0
        ]
    ]
]

tensorPart[t_, {}, ___] := t


(* tensorTranspose[t_Symbol ? AtomQ | t : TensorSymbol[__], perm_] := setDimesions[t, Permute[tensorDimensions[t], perm]] *)

tensorTranspose[t_, perm_] := Transpose[t, perm]
