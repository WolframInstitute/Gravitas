Package["WolframInstitute`Gravitas`IndexArray`ArrayUtilities`"]

PackageImport["WolframInstitute`Gravitas`Utilities`"]

PackageExport[ArrayDimensions]
PackageExport[ArrayRank]
PackageExport[ArraySymmetry]
PackageExport[ArrayName]
PackageExport[ArrayPart]
PackageExport[ArrayTranspose]

PackageExport[squareMatrixQ]

PackageExport[setDimensions]

PackageExport[EinsteinSummation]



ClearAll[ArrayDimensions, ArrayRank, ArrayName, ArrayPart, ArrayTranspose, squareMatrixQ, setDimensions, EinsteinSummation]


ArrayDimensions[t_] := Replace[TensorDimensions[t], Except[_List] :> {}]

ArrayDimensions[Inactive[D][t_, {d_List, n : _Integer ? NonNegative : 1}]] := Join[ArrayDimensions[t], ConstantArray[Length[d], n]]
ArrayDimensions[Inactive[D][t_, __]] := ArrayDimensions[t]

ArrayDimensions[Verbatim[Transpose][t_, perm : _Cycles | _List : {2, 1}]] := Permute[ArrayDimensions[t], perm]
ArrayDimensions[Verbatim[Transpose][t_, k_Integer]] := RotateRight[ArrayDimensions[t], k]
ArrayDimensions[Verbatim[Transpose][t_, m_Integer <-> n_Integer]] := Permute[ArrayDimensions[t], Cycles[{{m, n}}]]

ArrayDimensions[Inactive[TensorProduct][ts__]] := Catenate[ArrayDimensions /@ {ts}]

ArrayDimensions[Verbatim[Plus][ts___]] := With[{dims = ArrayDimensions /@ {ts}}, {n = Max[Length /@ dims]},
    TakeWhile[Thread[PadRight[#, n, 1] & /@ dims], Apply[Equal]][[All, 1]]
]

ArrayDimensions[IgnoringInactive[TensorContract[t_, c : {{___Integer} ...}]]] := Delete[ArrayDimensions[t], List /@ Catenate[c]]


ArrayRank[t_] := Length[ArrayDimensions[t]]

ArraySymmetry[t_] := Replace[TensorSymmetry[t], Except[_Symmetric | _Antisymmetric | _ZeroSymmetric] -> {}]


SymbolicArray = VectorSymbol | MatrixSymbol | ArraySymbol

ArrayAssumptionSymbol = Vectors | Matrices | Arrays


ArrayName[t_Symbol ? AtomQ] := t

ArrayName[SymbolicArray[s_, ___]] := s

ArrayName[___] := None

squareMatrixQ[t_] := MatchQ[ArrayDimensions[t], {n_, n_} | {_, 0}]


setDimensions[SymbolicArray[s_, _, dom_ : Reals, sym_ : {}], dims : {___Integer ? Positive}] := Switch[dims,
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
    $Assumptions = ToList[$Assumptions];
    pos = FirstPosition[$Assumptions, Element[s, _], Missing[], {1}, Heads -> False];
    If[ MissingQ[pos],
        AppendTo[$Assumptions, newElement[defDom, defSym]],
        $Assumptions //= ReplacePart[
            pos -> Replace[
                Extract[$Assumptions, pos],
                Element[_, ArrayAssumptionSymbol[_, dom_ : defDom, sym_ : defSym]] :> newElement[dom, sym]
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


ArrayPart[t_, {i_, is___}, k_ : 0] := With[{nest = Nest[#[] &, #, k] &},
    If[ i === All,
        ArrayPart[t, {is}, k + 1],
        ArrayPart[
            Replace[
                t,
                {
                    (VectorSymbol | ArraySymbol)[s_, {_} | _Integer, dom___] /; k < 1 :> ArraySymbol[nest[s][i], {}, dom],
                    (MatrixSymbol | ArraySymbol)[s_, ds : {_, _}, dom_ : Reals, ___] /; k < 2 :> VectorSymbol[nest[s][i], Drop[ds, {k + 1}], dom],
                    HoldPattern[ArraySymbol[s_, ds_List, dom_, ___]] /; k < Length[ds] :> If[Length[ds] - k == 3, MatrixSymbol, ArraySymbol][nest[s][i], Drop[ds, {k + 1}], dom],
                    s_Symbol ? AtomQ :> setDimensions[s, Drop[ArrayDimensions[t], {k + 1}]],
                    _ :> (Part[t, ##] & @@ Append[ConstantArray[All, k], i])
                }
            ],
            {is},
            0
        ]
    ]
]

ArrayPart[t_, {}, ___] := t


(* ArrayTranspose[t_Symbol ? AtomQ | t : SymbolicArray[__], perm_] := setDimesions[t, Permute[ArrayDimensions[t], perm]] *)

ArrayTranspose[t_, perm_] := Transpose[t, Replace[perm, m_ <-> n_ :> Cycles[{{m, n}}]]]

ArrayTranspose[Verbatim[Transpose][t_, perm1_], perm2_] := ArrayTranspose[t, PermutationList[PermutationProduct[perm1, perm2]]]


ArrayContract[array_, c_] := Replace[TensorContract[array, c], Inactive[TensorProduct][t_] :> t]

ArrayContract[arrays_List, c_] := ArrayContract[Inactive[TensorProduct] @@ arrays, c]




EinsteinSummation[in_List | (in_List -> Automatic), arrays_] := Module[{
	res = isum[in -> Cases[Tally @ Flatten @ in, {_, 1}][[All, 1]], arrays]
},
	res /; res =!= $Failed
]

EinsteinSummation[in_List -> out_, arrays_] := isum[in -> out, arrays]

EinsteinSummation[s_String, arrays_] := EinsteinSummation[
	Replace[
		StringSplit[s, "->"],
		{{in_, out_} :> Characters[StringSplit[in, ","]] -> Characters[out],
		{in_} :> Characters[StringSplit[in, ","]]}
	],
	arrays
]

hadamardProduct[indices_, arrays_] := Block[{
    dims = DeleteDuplicatesBy[Catenate @ MapThread[Thread[#1 -> Dimensions[#2]] &, {indices, arrays}], First],
    newIndices, posIndex
},
    newIndices = (is |-> Select[Keys[dims], MemberQ[is, #] &]) /@ indices;
    posIndex = First /@ PositionIndex[Keys[dims]];
    {
        Keys[dims],
        Times @@ MapThread[
            ArrayPad[
                #,
                {0, #} & /@ (Values[dims] - Dimensions[#]),
                "Fixed"
            ] & @ ArrayReshape[
                Transpose[#3, FindPermutation[#1, #2]],
                ReplacePart[ConstantArray[1, Length[posIndex]], Thread[Lookup[posIndex, #2, {}] -> Dimensions[#3]]]
            ] &,
            {indices, newIndices, arrays}
        ]
    }
]

isum[in_List -> out_, arrays_List] := Enclose @ Module[{
	nonFreePos, freePos, nonFreeIn, nonFreeArray,
    newArrays, newIn, indices, dimensions, contracted, contractions, multiplicity, tensor, transpose
},
	If[ Length[in] != Length[arrays],
        Message[EinsteinSummation::length, Length[in], Length[arrays]];
	    Confirm[$Failed]
    ];
	MapThread[
		If[ VectorQ[#1] && Length[#1] != ArrayRank[#2],
			Message[EinsteinSummation::shape, #1, #2];
            Confirm[$Failed]
		] &,
		{in, arrays}
	];
    If[ AnyTrue[out, Count[in, {___, #, ___}] > 1 &],
        nonFreePos = Catenate @ Position[in, _ ? (ContainsAny[out]), {1}, Heads -> False];
        freePos = Complement[Range[Length[in]], nonFreePos];
        {nonFreeIn, nonFreeArray} = hadamardProduct[in[[nonFreePos]], arrays[[nonFreePos]]];
        newArrays = Prepend[arrays[[freePos]], nonFreeArray];
        newIn = Prepend[in[[freePos]], nonFreeIn]
        ,
        newArrays = arrays;
        newIn = in
    ];
	indices = Catenate[newIn];
    dimensions = Catenate[ArrayDimensions /@ newArrays];
	contracted = DeleteElements[indices, 1 -> out];
	contractions = Flatten[Take[Position[indices, #[[1]], {1}, Heads -> False], UpTo[#[[2]]]]] & /@ Tally[contracted];
    If[! AllTrue[contractions, Equal @@ dimensions[[#]] &], Message[EinsteinSummation::dim]; Confirm[$Failed]];
	indices = DeleteElements[indices, 1 -> contracted];
	If[! ContainsAll[indices, out], Message[EinsteinSummation::output]; Confirm[$Failed]];
    tensor = ArrayContract[newArrays, contractions];
	multiplicity = Max @ Merge[{Counts[out], Counts[indices]}, Apply[Ceiling[#1 / #2] &]];
	If[ multiplicity > 1,
		indices = Catenate @ ConstantArray[indices, multiplicity];
		contracted = DeleteElements[indices, 1 -> out];
		contractions = Flatten[Take[Position[indices, #[[1]]], #[[2]]]] & /@ Tally[contracted];
		indices = DeleteElements[indices, 1 -> contracted];
		tensor = ArrayContract[ConstantArray[tensor, multiplicity], contractions];
	];
	transpose = FindPermutation[indices, out];
	Transpose[tensor, transpose]
]

EinsteinSummation::length = "Number of index specifications (`1`) does not match the number of tensors (`2`)";
EinsteinSummation::shape = "Index specification `1` does not match the tensor rank of `2`";
EinsteinSummation::dim = "Dimensions of contracted indices don't match";
EinsteinSummation::output = "The uncontracted indices can't compose the desired output";

