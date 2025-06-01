Package["WolframInstitute`Gravitas`"]

PackageImport["WolframInstitute`Gravitas`Utilities`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`TensorUtilities`"]

PackageExport[IndexTensorQ]
PackageExport[IndexTensor]
PackageExport[IndexContract]
PackageExport[IndexJuggling]



ClearAll[indexTensorQ, IndexTensorQ, IndexTensor, IndexContract, Prop]

(* Validation *)

metricQ[ia_] := IndexArrayQ[ia] && MatchQ[ia["SignedDimensions"], {x_, x_}]

indexTensorQ[IndexTensor[ia_IndexArray, gs : {({__Integer ? Positive} -> _IndexArray | None) ...}, ___]] :=
    IndexArrayQ[ia] && AllTrue[gs[[All, 2]], # === None || metricQ[#] &] &&
    With[{indices = ia["Indices"]},
        AllTrue[Catenate[gs[[All, 1]]], 0 < # <= Length[indices] &] && AllTrue[gs, #[[2]] === None || AllTrue[Through[Select[indices[[#[[1]]]], #["FreeQ"] &]["Dimension"]], EqualTo[#[[2]]["Dimensions"][[1]]]] &]
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

IndexTensor["Properties"] := Join[{"IndexArray", "Metrics", "MetricRules", "MetricQ", "ChristoffelSymbol"}, IndexArray["Properties"]]

Prop[_, "Properties"] := IndexTensor["Properties"]

Prop[IndexTensor[ia_, ___] ? IndexTensorQ, "IndexArray"] := ia

Prop[IndexTensor[_, g_] ? IndexTensorQ, "Metrics"] := g

Prop[IndexTensor[g_] ? IndexTensorQ, "Metrics"] := Sequence[]

Prop[IndexTensor[_], "MetricQ"] := True
Prop[_, "MetricQ"] := False

Prop[it_, "MetricRules"] := With[{metrics = If[it["MetricQ"], {Range[it["Rank"]] -> it["IndexArray"]}, it["Metrics"]]},
    Join[
        MapAt[If[#["SignedDimensions"][[1]] > 0, Inverse[#], #] &, metrics, {All, 2}],
        Values @ GroupBy[Thread[# -> it["Dimensions"][[#]]], #[[2]] &, #[[All, 1]] -> IndexArray[IdentityMatrix[#[[1, 2]]], "I"] &] & @
            Complement[it["FreeIndexPositions"], Catenate[metrics[[All, 1]]]]
    ]
]

Prop[it_, prop_String, args___] /; MemberQ[IndexArray["Properties"], prop] := it["IndexArray"][prop, args]

Prop[it_, "Tensor"] := it["IndexArray"]["Array"]

Prop[it_, "Coordinates"] := it["Parameters"]

Prop[it_, "ChristoffelSymbol" | "ChristoffelSymbols"] := ChristoffelSymbols[it]

Prop[_, prop_String, ___] := Missing[prop]


(* General constructors *)

IndexTensor[arg : Except[_IndexArray | _IndexTensor]] := With[{ia = IndexArray[arg]}, If[metricQ[ia], IndexTensor[ia], IndexTensor[ia, {}]]]

IndexTensor[arg : Except[_IndexArray | _IndexTensor], args___] := IndexTensor[IndexArray[arg, args]]

IndexTensor[arg : Except[_IndexArray | _IndexTensor], args___, metric : _ ? metricQ | {({__Integer} -> _ ? metricQ) ..}] := IndexTensor[IndexArray[arg, args], metric]

IndexTensor[arg : Except[_IndexArray | _IndexTensor], args___, metric_ ? IndexTensorQ] /; metric["MetricQ"] := IndexTensor[IndexArray[arg, args], metric["IndexArray"]]

IndexTensor[ia_ ? IndexArrayQ, metric_ ? IndexArrayQ] /; metricQ[metric] := IndexTensor[ia, {ia["FreeIndexPositions"] -> metric}]

IndexTensor[ia_ ? IndexArrayQ] /; ! metricQ[ia] := IndexTensor[ia, {}]


(* Index juggling *)

IndexContract[tensors : {__ ? IndexTensorQ}, output : _List | Automatic : Automatic, prop_String : "Tensor"] := Enclose @ Block[{
	arrays, metrics, metricIndices, tensorIndices, indexPositions, contractions, newShape, contractedIndexPositions, reindexMetrics, reindex, reindexedArrays
},
	arrays = Through[tensors["IndexArray"]];
	metrics = Through[tensors["MetricRules"]];
	metricIndices = Through[metrics["FreeIndices"]];
	tensorIndices = MapThread[
		If[#1["FreeQ"], {#1, #2, Replace[#2[[3]], Append[Catenate[Thread /@ metrics[[#2[[1]]]]], _ -> None]]}, Nothing] &,
		{Catenate @ Through[tensors["FreeIndices"]], Catenate @ MapIndexed[Append[#2, #1] &, Through[tensors["FreeIndexPositions"]], {2}]}
	];
	contractions = Values[Take[#, 2] & /@ Select[GroupBy[Cases[tensorIndices, {_, _, Except[None]}], ({#[[1]]["Name"], Simplify @ Normal[#[[3]]]} &)], Length[#] > 1 &]];
	contractions = #[[All, ;; 2]] -> If[Equal @@ Through[#[[All, 1]]["Variance"]], #[[1, 3]], None] & /@ contractions;
    indexPositions = Catenate @ MapIndexed[#2 &, Through[tensors["Indices"]], {2}];
	contractedIndexPositions = Lookup[PositionIndex[indexPositions], Catenate[contractions[[All, 1, All, 2, {1, 3}]]]];
    newShape = Delete[Catenate[Through[tensors["Indices"]]], contractedIndexPositions];
    metrics = Delete[tensorIndices[[All, 3]], contractedIndexPositions];
    If[ output =!= Automatic, 
        With[{outPositions = Take[Catenate @ Lookup[PositionIndex[Through[newShape["Name"]]], output, Nothing], UpTo[Length[output]]]},
            newShape = newShape[[outPositions]];
            metrics = metrics[[outPositions]];
        ]
    ];

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
        ConfirmQuiet[EinsteinSummation[Map[#["Name"] &, Through[reindexedArrays["FreeIndices"]], {2}] -> output, Through[reindexedArrays["Array"]]]],
        newShape,
        DeleteDuplicates[Catenate[Through[tensors["Parameters"]]]],
        DeleteDuplicates[Catenate[Through[tensors["Assumptions"]]]],
        If[Length[tensors] == 1, tensors[[1]]["Name"], None]
        (* Replace[CircleTimes @@ Through[tensors["Symbol"]], CircleTimes[x_] :> x] *)
    ];
    If[prop === "Array", Return[newArray]];

    IndexTensor[
        newArray,
        #[[All, 1]] -> #[[1, 2]] & /@ Values @ GroupBy[Thread[newArray["FreeIndexPositions"] -> metrics], (Normal[#[[2]]] &)]
    ]
]

IndexContract[array_ ? IndexArrayQ, args___] := IndexContract[{array}, args]

IndexContract[arrays_List, metric_ ? IndexTensorQ, args___] := IndexContract[arrays, metric["IndexArray"], args]

IndexContract[arrays_List, metric_ ? IndexArrayQ, args___] := IndexContract[IndexTensor[#, metric] & /@ arrays, args]

IndexContract[tensor_ ? IndexTensorQ, args___] := IndexContract[{tensor}, args]


it_IndexTensor[[is__]] ^:= Block[{
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
        IndexTensor[newArray, it["Metrics"]]
     ) /; AnyTrue[js, IntegerQ]
]

it_IndexTensor[[is__]] ^:= it

ia_IndexArray[rules : (_Integer -> _) ..] := With[{r = ia["Rank"]}, ia[[##]] & @@ ReplacePart[ConstantArray[All, r], Cases[{rules}, (k_ -> _) /; 0 < k <= r]]]


renameShape[shape_, renames_] := SubsetMap[
    MapThread[
        {i, name} |-> If[MatchQ[name, - _], Dimension[i, - name]["Lower"], Dimension[i, name]["Upper"]],
        {#, renames[[All, 2]]}
    ] &,
    shape,
    renames[[All, 1]]
]


(it : _IndexTensor ? IndexTensorQ)[is___] := IndexJuggling[it, {is}]


IndexJuggling[it_, {}] := it

IndexJuggling[it_, shape_Shape ? ShapeQ] := IndexJuggling[it, Through[shape["Indices"]["SignedName"]]]

IndexJuggling[it : _ ? IndexTensorQ | _ ? IndexArrayQ, newIndices_List] := Enclose @ Block[{
    indices = it["Indices"], indexPositions = it["FreeIndexPositions"],
    l, n, m,
    names, newNames = SignedSymbolName /@ Replace[newIndices, d_Dimension :> d["SignedName"], 1], rules, perm, renames, newShape, renamedShape, newArray, newTensor, vars
},
    l = Length[indices];
    n = Length[newNames];
    m = Min[l, n];
    names = First /@ PositionIndex[Through[indices["Name"]]];
    rules = MapThread[
        With[{i = Lookup[names, Key[CanonicalSymbolName[#1]]]},
            i -> {#2, #3, MissingQ[i] || MatchQ[#1, - _] != indices[[i]]["LowerQ"]}
        ] &,
        {Take[newNames, UpTo[m]], Take[indexPositions, UpTo[m]], Range[m]}
    ];
    rules = Catenate @ Values @ GroupBy[rules, First, Prepend[First[#]] @ Map[Missing[] -> #[[2]] &, Rest[#]] &];
    perm = FindPermutation[Join[#, DeleteElements[indexPositions, #]]] & @
        Map[If[MissingQ[#[[1]]], Replace[Replace[#[[2, 1]], rules], {x_, __} :> Replace[Replace[x, rules], {y_, __} :> y]], #[[1]]] &, rules];
    renames = Cases[rules, (_ -> {k_, l_, True}) :> k -> newNames[[l]]];
    newShape = Permute[indices, perm];
    rules = Thread[indexPositions -> Permute[indexPositions, InversePermutation[perm]]];
    newArray = IndexArray[
        tensorTranspose[it["Array"], perm],
        newShape,
        it["Parameters"], it["Assumptions"], it["Name"]
    ];
    renamedShape = renameShape[newShape, renames];
    If[IndexArrayQ[it], Return[IndexArray[newArray, renamedShape]]];

    newTensor = IndexTensor[newArray, MapAt[Replace[#, rules, 1] &, it["MetricRules"], {All, 1}]];
    rules = Append[_ -> None] @ Catenate[Thread /@ newTensor["Metrics"]];
    vars = MapThread[With[{metric = Replace[#3, rules]},
            If[ ! #1["FreeQ"] || #1["Variance"] == #2["Variance"] || metric === None,
                #2,
                {#3, {FreshVariable["i"], #2["Name"]}, #1["Variance"]}
            ]
        ] &,
        {newShape, renamedShape, Range[l]}
    ];
    newTensor = ConfirmBy[
        IndexContract[
            {
                IndexTensor[newArray @@ Replace[vars, {{_, {v_, _}, s_} :> s * v, d_Dimension :> d["SignedName"]}, 1], newTensor["Metrics"]],
                Splice[
                    With[{metric = Replace[#[[1]], rules], rename = #[[2]], variance = #[[3]]},
                        If[ metric === None,
                            Nothing,
                            With[{sign = Sign[metric["SignedDimensions"][[1]]]},
                                IndexTensor[If[variance == sign, Inverse[metric] @@ (- sign * rename), metric @@ (sign * rename)], metric]
                            ]
                        ]
                    ] & /@ Cases[vars, _List]
                ]
            },
            Join[Replace[vars, {d_Dimension :> d["Name"], {_, {_, v_}, _} :> v}, 1], CanonicalSymbolName /@ Drop[newNames, UpTo[m]]]
        ],
        IndexTensorQ
    ];
    newShape = Through[newTensor["Indices"]["SignedName"]];
    
    If[ n < l && Take[newShape, UpTo[n]] =!= Take[newNames, UpTo[n]],
        newTensor = newTensor @@ Join[newNames, Drop[newShape, UpTo[n]]]
    ];

    If[ n > l && Drop[newShape, UpTo[m]] =!= Drop[newNames, UpTo[m]],
        newTensor = newTensor @@ newNames
    ];

    If[ it["MetricQ"] && metricQ[newTensor["IndexArray"]],
        newTensor = IndexTensor[newTensor["IndexArray"]]
    ];

    IndexTensor[newTensor, it["Name"]]
]


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


IndexTensor /: D[it_IndexTensor, i_] /; it["MetricQ"] :=
 	IndexTensor[
  		Transpose[D[it["Array"], #] & /@ it["Coordinates"], {3, 1, 2}],
  		Append[Dimension[- Length[it["Coordinates"]], i]] @ it["Indices"],
  		it["Coordinates"], it["Assumptions"],
  		Row[{"\[PartialD]", it["Name"]}],
  		it
  	]

IndexTensor /: Times[it_IndexTensor ? IndexTensorQ, xs___] :=
 	IndexTensor[
        Times[it["Array"], xs],
        it["Shape"], it["Parameters"], it["Assumptions"], 
        Times[xs] it["Name"],
        it["Metrics"]
    ]

IndexTensor /: Plus[its__IndexTensor] := Block[{
   	indices = Through[{its}["FreeIndices"]],
   	setIndices, newTensors
 },
  	(
        setIndices = {its}[[1]]["FreeIndices"];
        newTensors = # @@ setIndices & /@ {its};
        IndexTensor[
            Total[Through[newTensors["Array"]]],
            setIndices,
            DeleteDuplicates @ Catenate[Through[{its}["Parameters"]]],
            DeleteDuplicates @ Catenate[Through[{its}["Assumptions"]]],
            Total[Through[{its}["Name"]]],
            {its}[[1]]["Metrics"]
        ]
    ) /; SameQ @@ Sort /@ Map[{#["Name"], #["Dimension"]} &, indices, {2}]
]


(* Formatting *)

IndexTensor /: MakeBoxes[it_IndexTensor /; IndexTensorQ[Unevaluated[it]], TraditionalForm] := With[{
    boxes = ToBoxes[Normal[it], TraditionalForm]
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
                If[it["MetricQ"], BoxForm`SummaryItem[{"Metric"}], Nothing]
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

