Package["WolframInstitute`Gravitas`"]

PackageImport["WolframInstitute`Gravitas`Utilities`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`TensorUtilities`"]

PackageExport[IndexTensorQ]
PackageExport[IndexTensor]
PackageExport[IndexContract]



ClearAll[indexTensorQ, IndexTensorQ, IndexTensor, IndexContract, Prop]

(* Validation *)

metricQ[ia_] := IndexArrayQ[ia] && MatchQ[DeleteDuplicates[ia["SignedDimensions"]], {_Integer}]

indexTensorQ[IndexTensor[ia_IndexArray, gs : {({__Integer ? Positive} -> _IndexArray) ...}, ___]] :=
    IndexArrayQ[ia] && AllTrue[gs[[All, 2]], metricQ] &&
    With[{indices = ia["Indices"]},
        AllTrue[Catenate[gs[[All, 1]]], 0 < # <= Length[indices] &] && AllTrue[gs, AllTrue[Through[Select[indices[[#[[1]]]], #["FreeQ"] &]["Dimension"]], EqualTo[#[[2]]["Dimensions"][[1]]]] &]
    ]

indexTensorQ[IndexTensor[g_IndexArray]] := metricQ[g]

indexTensorQ[___] := False


IndexTensorQ[it_IndexTensor] := System`Private`HoldValidQ[it] || indexTensorQ[Unevaluated[it]]

IndexTensorQ[___] := False


(* Mutation *)

IndexTensor[it_IndexTensor, args___] := With[{newArray = IndexArray[it["IndexArray"], args]},
    If[it["MetricQ"] && metricQ[newArray], IndexTensor[newArray], IndexTensor[newArray, it["Metrics"]]]
]


it_IndexTensor /; System`Private`HoldNotValidQ[it] && indexTensorQ[Unevaluated[it]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[it]]


(* Properties *)

(it_IndexTensor ? IndexTensorQ)[prop_String | prop_String[args___]] := Prop[it, prop, args] = Prop[it, prop, args]

IndexTensor["Properties"] := Join[{"IndexArray", "Metrics", "MetricRules", "MetricQ"}, IndexArray["Properties"]]

Prop[_, "Properties"] := IndexTensor["Properties"]

Prop[IndexTensor[ia_, ___] ? IndexTensorQ, "IndexArray"] := ia

Prop[IndexTensor[_, g_] ? IndexTensorQ, "Metrics"] := g

Prop[IndexTensor[g_] ? IndexTensorQ, "Metrics"] := {Range[g["Rank"]] -> g}

Prop[IndexTensor[_], "MetricQ"] := True
Prop[_, "MetricQ"] := False

Prop[it_, "MetricRules"] := With[{metrics = it["Metrics"]},
    Join[metrics, Values @ GroupBy[Thread[# -> it["Dimensions"][[#]]], #[[2]] &, #[[All, 1]] -> IndexArray[IdentityMatrix[#[[1, 2]]], "I"] &] & @ Complement[it["FreeIndexPositions"], Catenate[metrics[[All, 1]]]]]
]

Prop[it_, prop_String, args___] /; MemberQ[IndexArray["Properties"], prop] := it["IndexArray"][prop, args]

Prop[it_, "Tensor"] := it["IndexArray"]["Array"]

Prop[it_, "Coordinates"] := it["Parameters"]

Prop[_, prop_String, ___] := Missing[prop]


(* General constructor *)

IndexTensor[tensor : Except[_IndexArray | _IndexTensor]] := With[{ia = IndexArray[tensor]}, If[metricQ[ia], IndexTensor[ia], IndexTensor[ia, {}]]]

IndexTensor[tensor : Except[_IndexArray | _IndexTensor], args__] := IndexTensor[IndexArray[tensor], IndexArray[args]]

IndexTensor[tensor_ ? IndexArrayQ, metric_ ? IndexArrayQ] := IndexTensor[tensor, {tensor["FreeIndexPositions"] -> metric}]


(* Index juggling *)

IndexContract[tensors : {__ ? IndexTensorQ}, output : _List | Automatic : Automatic, prop_String : "Tensor"] := Enclose @ Block[{
	arrays, metrics, metricIndices, tensorIndices, indexPositions, contractions, newShape, contractedFreePositions, contractedIndexPositions, reindexMetrics, reindex, reindexedArrays
},
	arrays = Through[tensors["IndexArray"]];
	metrics = Through[tensors["Metrics"]];
	metricIndices = Through[metrics["FreeIndices"]];
	tensorIndices = MapThread[
		If[#1["FreeQ"], {#1, #2, Replace[#2[[3]], Append[Catenate[Thread /@ metrics[[#2[[1]]]]], _ -> None]]}, Nothing] &,
		{Catenate @ Through[tensors["FreeIndices"]], Catenate @ MapIndexed[Append[#2, #1] &, Through[tensors["FreeIndexPositions"]], {2}]}
	];
	contractions = Values[Take[#, 2] & /@ Select[GroupBy[tensorIndices, ({#[[1]]["Name"], Normal[#[[3]]]} &)], Length[#] > 1 &]];
	contractions = #[[All, ;; 2]] -> If[Equal @@ Through[#[[All, 1]]["Variance"]], #[[1, 3]], None] & /@ contractions;
	contractedFreePositions = List /@ Catenate @ Lookup[PositionIndex[Through[tensorIndices[[All, 1]]["Name"]]], Through[Catenate[contractions[[All, 1, All, 1]]]["Name"]]];
    indexPositions = Catenate @ MapIndexed[#2 &, Through[tensors["Indices"]], {2}];
	contractedIndexPositions = Lookup[PositionIndex[indexPositions], Catenate[contractions[[All, 1, All, 2, {1, 3}]]]];
    newShape = Delete[Catenate[Through[tensors["Indices"]]], contractedIndexPositions];
    newShape = Replace[output, {
        Automatic -> newShape,
        _ :> With[{outPositions = Lookup[PositionIndex[Through[newShape["Name"]]], output, Nothing]},
            SubsetMap[Extract[#, outPositions] &, newShape, Sort[outPositions]]
        ]
    }];

    If[prop === "Shape", Return[newShape]];
	reindexMetrics = Map[
		With[{inverseQ = #[[1, 1, 1]]["LowerQ"], names = FreshVariable /@ {"i", "j"}},
			MapThread[#1[[1]] -> #1[[2]] -> If[inverseQ, 1, -1] * #2 &, {#[[1, All, 2]], names}] ->
				If[inverseQ, Inverse[#[[2]]] @@ (- names), #[[2]] @@ names]
		] &, 
		Cases[contractions, HoldPattern[_ -> _IndexArray]]
	];
	reindex = GroupBy[Catenate[reindexMetrics[[All, 1]]], First -> Last];
	reindexedArrays = Join[
		MapIndexed[
			With[{newIndex = Lookup[reindex, #2[[1]]]},
				If[MissingQ[newIndex], #1, #1 @@ newIndex]
			] &,
			arrays
		],
		reindexMetrics[[All, 2]]
	];
    If[prop === "Arrays", Return[reindexedArrays]];
    newArray = IndexArray[
        EinsteinSummation[Map[#["Name"] &, Through[reindexedArrays["FreeIndices"]], {2}] -> output, Through[reindexedArrays["Array"]]],
        newShape,
        DeleteDuplicates[Catenate[Through[tensors["Parameters"]]]],
        DeleteDuplicates[Catenate[Through[tensors["Assumptions"]]]],
        If[Length[tensors] == 1, tensors[[1]]["Name"], None]
        (* Replace[CircleTimes @@ Through[tensors["Symbol"]], CircleTimes[x_] :> x] *)
    ];
    If[prop === "Array", Return[newArray]];

    IndexTensor[
        newArray,
        #[[All, 1]] -> #[[1, 2]] & /@ Values @ GroupBy[Thread[newArray["FreeIndexPositions"] -> Delete[tensorIndices[[All, 3]], contractedFreePositions]], (Normal[#[[2]]] &)]
    ]
]

IndexContract[array_ ? IndexArrayQ, args___] := IndexContract[{array}, args]

IndexContract[arrays_List, metric_ ? IndexTensorQ, args___] := IndexContract[arrays, metric["IndexArray"], args]

IndexContract[arrays_List, metric_ ? IndexArrayQ, args___] := IndexContract[IndexTensor[#, metric] & /@ arrays, args]

IndexContract[tensor_ ? IndexTensorQ, args___] := IndexContract[{tensor}, args]


it_IndexTensor[is__] := Block[{
    indices = it["Indices"], js, newArray
},
    js = MapThread[If[MatchQ[#2, _Integer | All], #2, Lookup[#1, Key[#2]]] &, {Map[First] @* PositionIndex /@ Through[Take[indices, UpTo[Length[{is}]]]["Indices"]], {is}}];
    (
        newArray = IndexArray[
            tensorPart[it["Array"], Replace[js, _Missing -> All, 1]],
            MapThread[
                If[ IntegerQ[#2],
                    Dimension[#1, Mod[#2, #1["Dimension"], 1]],
                    Replace[#2, {
                        Missing[_, - name_] :> Dimension[#1, name]["Lower"],
                        Missing[_, name_] :> Dimension[#1, name]["Upper"]
                    }]
                ] &, 
                {indices, ReplacePart[indices, Thread[Take[Select[indices, (#["FreeQ"] &) -> "Index"], UpTo[Length[js]]] -> js]]}
            ],
            it["Parameters"], it["Assumptions"], it["Name"]
        ];
        If[metricQ[newArray], IndexTensor[newArray], IndexTensor[newArray, it["Metrics"]]]
     ) /; AnyTrue[js, IntegerQ]
]

it_IndexTensor[] := it

renameShape[shape_, renames_] := SubsetMap[
    MapThread[
        {i, name} |-> If[MatchQ[name, - _], Dimension[i, - name]["Lower"], Dimension[i, name]["Upper"]],
        {#, renames[[All, 2]]}
    ] &,
    shape,
    renames[[All, 1]]
]

it_IndexTensor[is__] := Block[{
    indices = it["Indices"], indexPositions = it["FreeIndexPositions"], n, m, names, repl, perm, order, renames, newShape, renamedShape, newArray, newTensor
},
    n = Length[{is}];
    m = Length[indices];
    names = First /@ PositionIndex[Through[indices["Name"]]];
    repl = MapThread[
        With[{minusQ = MatchQ[#1, - _]},
            Lookup[names, Key[CanonicalSymbolName[If[minusQ, - #1, #1]]]] -> {#2, #3, minusQ != indices[[#2]]["LowerQ"]}
        ] &,
        {{is}, Take[indexPositions, UpTo[n]], Range[n]}
    ];
    repl = Catenate @ Values @ GroupBy[repl, First, Prepend[First[#]] @ Map[Missing[] -> #[[2]] &, Rest[#]] &];
    perm = FindPermutation[Join[#, DeleteElements[indexPositions, #]]] & @
        Map[If[MissingQ[#[[1]]], Replace[Replace[#[[2, 1]], repl], {x_, __} :> Replace[Replace[x, repl], {y_, __} :> y]], #[[1]]] &, repl];
    order = PermutationList @ InversePermutation @ perm;
    renames = Cases[repl, (_Missing -> {k_, l_, _}) | (_ -> {k_, l_, True}) :> k -> {is}[[l]]];
    newShape = Permute[indices, perm];
    repl = Thread[indexPositions -> Permute[indexPositions, InversePermutation[perm]]];
    newArray = IndexArray[
        tensorTranspose[it["Array"], perm],
        newShape,
        it["Parameters"], it["Assumptions"], it["Name"]
    ];
    newTensor = IndexTensor[newArray, MapAt[Replace[#, repl, 1] &, it["Metrics"], {All, 1}]];
    repl = Append[_ -> None] @ Catenate[Thread /@ newTensor["Metrics"]];
    renamedShape = renameShape[newShape, renames];
    With[{
        vars = MapThread[With[{metric = Replace[#3, repl]},
                If[ ! #1["FreeQ"] || #1["Variance"] == #2["Variance"] || metric === None,
                    #2["SignedName"],
                    {#3, {FreshVariable["i"], #2["Name"]}, #1["Variance"]}
                ]
            ] &,
            {newShape, renamedShape, Range[m]}
        ]
    },
        newTensor = IndexContract[
            {
                IndexTensor[newArray @@ Replace[vars, {_, {v_, _}, s_} :> s * v, 1], newTensor["Metrics"]],
                Splice[
                    With[{metric = Replace[#[[1]], repl], rename = #[[2]], variance = #[[3]]},
                        With[{sign = Sign[metric["SignedDimensions"][[1]]]},
                            IndexTensor[If[variance == sign, Inverse[metric] @@ (- sign * rename), metric @@ (sign * rename)], metric]
                        ]
                    ] & /@ Cases[vars, _List]
                ]
            },
            Through[renamedShape["Name"]]
        ];
        
        If[ metricQ[newTensor["IndexArray"]],
            newTensor = IndexTensor[newTensor["IndexArray"]]
        ];

        IndexTensor[newTensor, it["Name"]]
    ]
]

ia_IndexArray[rules : (_Integer -> _) ..] := With[{r = ia["Rank"]}, ia @@ ReplacePart[ConstantArray[All, r], Cases[{rules}, (k_ -> _) /; 0 < k <= r]]]


(* UpValues *)

Scan[
    Function[f,
        IndexTensor /: f[it_IndexTensor ? IndexTensorQ, args___] := f[it["IndexArray"], args]
    ],
    {Normal, Dimensions, SquareMatrixQ}
]

Scan[
    Function[f,
        IndexTensor /: f[it_IndexTensor ? IndexTensorQ, args___] := If[it["MetricQ"], IndexTensor[#], IndexTensor[#, it["Metrics"]]] & @ f[it["IndexArray"], args]
    ],
    {Inverse}
]


(* Formatting *)

IndexTensor /: MakeBoxes[it_IndexTensor /; IndexTensorQ[Unevaluated[it]], TraditionalForm] := With[{
    boxes = ToBoxes[it["Symbol"], TraditionalForm]
},
    InterpretationBox[
        boxes,
        it
    ]
]
    

IndexTensor /: MakeBoxes[it_IndexTensor /; IndexTensorQ[Unevaluated[it]], form_] :=
    BoxForm`ArrangeSummaryBox["IndexTensor", it, it["Icon"],
        {
            {
                BoxForm`SummaryItem[{"Symbol: ", it["Symbol"]}],
                BoxForm`SummaryItem[{"Metric: ", If[it["MetricQ"], "Yes", "No"]}]
            },
            {
                BoxForm`SummaryItem[{"Dimensions: ", it["Dimensions"]}], 
                BoxForm`SummaryItem[{"Coordinates: ", it["Coordinates"]}]   
            }
        },
        {
            {
                BoxForm`SummaryItem[{"Symmetry: ", it["Symmetry"]}],
                BoxForm`SummaryItem[{"Assumptions: ", it["Assumptions"]}]
            }
        },
        form,
        "Interpretable" -> Automatic
    ]


If[ $FrontEnd =!= Null,
    ResourceFunction["AddCodeCompletion"]["IndexTensor"][IndexTensor[]]
]

