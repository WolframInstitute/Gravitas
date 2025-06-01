Package["WolframInstitute`Gravitas`Utilities`"]

PackageExport[ToList]
PackageExport[FreshVariable]
PackageExport[CanonicalSymbolName]
PackageExport[SignedSymbolName]
PackageExport[EinsteinSummation]



ClearAll[ToList, FreshVariable, CanonicalSymbolName, SignedSymbolName, EinsteinSummation]


ToList = Developer`ToList


FreshVariable[name_String] := Block[{$ModuleNumber = 1}, ToExpression[RowBox[{"Module", "[", "{", name, "}", ",", name, "]"}]]]


CanonicalSymbolName[s_Symbol ? AtomQ] := With[{t = Unevaluated @@ ResourceFunction["UnformalizeSymbols"][s, "DeferQ" -> True]}, SymbolName[t]]

CanonicalSymbolName[- s_] := CanonicalSymbolName[s]

CanonicalSymbolName[s_] := s


SignedSymbolName[- s_] := - SignedSymbolName[s]

SignedSymbolName[s_] := CanonicalSymbolName[s]


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
		If[ IntegerQ @ TensorRank[#1] && Length[#1] != TensorRank[#2],
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
    dimensions = Catenate[Dimensions /@ newArrays];
	contracted = DeleteElements[indices, 1 -> out];
	contractions = Flatten[Take[Position[indices, #[[1]], {1}, Heads -> False], UpTo[#[[2]]]]] & /@ Tally[contracted];
    If[! AllTrue[contractions, Equal @@ dimensions[[#]] &], Message[EinsteinSummation::dim]; Confirm[$Failed]];
	indices = DeleteElements[indices, 1 -> contracted];
	If[! ContainsAll[indices, out], Message[EinsteinSummation::output]; Confirm[$Failed]];
    tensor = Activate @ TensorContract[Inactive[TensorProduct] @@ newArrays, contractions];
	multiplicity = Max @ Merge[{Counts[out], Counts[indices]}, Apply[Ceiling[#1 / #2] &]];
	If[ multiplicity > 1,
		indices = Catenate @ ConstantArray[indices, multiplicity];
		contracted = DeleteElements[indices, 1 -> out];
		contractions = Flatten[Take[Position[indices, #[[1]]], #[[2]]]] & /@ Tally[contracted];
		indices = DeleteElements[indices, 1 -> contracted];
		tensor = Activate @ TensorContract[Inactive[TensorProduct] @@ ConstantArray[tensor, multiplicity], contractions];
	];
	transpose = FindPermutation[indices, out];
	If[ArrayQ[tensor], Transpose[tensor, transpose], tensor]
]

EinsteinSummation::length = "Number of index specifications (`1`) does not match the number of tensors (`2`)";
EinsteinSummation::shape = "Index specification `1` does not match the tensor rank of `2`";
EinsteinSummation::dim = "Dimensions of contracted indices don't match";
EinsteinSummation::output = "The uncontracted indices can't compose the desired output";
