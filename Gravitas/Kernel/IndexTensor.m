Package["WolframInstitute`Gravitas`"]

PackageImport["WolframInstitute`Gravitas`Utilities`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`"]
PackageImport["WolframInstitute`Gravitas`IndexArray`TensorUtilities`"]

PackageExport[IndexTensorQ]
PackageExport[IndexTensor]
PackageExport[IndexContract]



ClearAll[indexTensorQ, IndexTensorQ, IndexTensor, IndexContract, Prop]

(* Validation *)

metricQ[ia_] := IndexArrayQ[ia] && MatchQ[DeleteDuplicates[ia["SignedDimensions"]], {_Integer ? Positive}]


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

IndexTensor[it_IndexTensor, coordinates_List, {is__ ? BooleanQ}, assumptions_List, name_] :=
    IndexTensor[it["Tensor"], padCoordinates[coordinates, it["Dimension"]], is, assumptions, name]

IndexTensor[it_IndexTensor, coordinates_List, args___] := IndexTensor[IndexTensor[it, coordinates, it["Indices"], it["Assumptions"], it["Name"]], args]

IndexTensor[it_IndexTensor, coordinates_List, assumptions_List, args___] := IndexTensor[IndexTensor[it, coordinates, it["Indices"], assumptions, it["Name"]], args]

IndexTensor[it_IndexTensor, is__ ? BooleanQ, args___] := IndexTensor[IndexTensor[it, it["Coordinates"], Join[{is}, Drop[it["Indices"], UpTo[Length[{is}]]]], it["Assumptions"], it["Name"]], args]

IndexTensor[it_IndexTensor, coordinates_List, is__ ? BooleanQ, args___] := IndexTensor[IndexTensor[it, it["Coordinates"], {is}, it["Assumptions"], it["Name"]], args]

IndexTensor[it_IndexTensor, name_, args___] := IndexTensor[IndexTensor[it, it["Coordinates"], it["Indices"], it["Assumptions"], name], args]

IndexTensor[it_IndexTensor] := it


it_IndexTensor /; System`Private`HoldNotValidQ[it] && indexTensorQ[Unevaluated[it]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[it]]


(* Properties *)

(it_IndexTensor ? IndexTensorQ)[prop_String | prop_String[args___]] := Prop[it, prop, args] = Prop[it, prop, args]

IndexTensor["Properties"] := Join[{"IndexArray", "Metrics", "MetricQ"}, IndexArray["Properties"]]

Prop[_, "Properties"] := IndexTensor["Properties"]

Prop[IndexTensor[ia_, ___] ? IndexTensorQ, "IndexArray"] := ia

Prop[IndexTensor[_, g_] ? IndexTensorQ, "Metrics"] := g

Prop[IndexTensor[g_] ? IndexTensorQ, "Metrics"] := {Range[g["Rank"]] -> g}

Prop[IndexTensor[_], "MetricQ"] := True
Prop[_, "MetricQ"] := False

Prop[it_, prop_String, args___] /; MemberQ[IndexArray["Properties"], prop] := it["IndexArray"][prop, args]

Prop[it_, "Tensor"] := it["IndexArray"]["Array"]

Prop[it_, "Coordinates"] := it["Parameters"]

Prop[_, prop_String, ___] := Missing[prop]


(* General constructor *)

IndexTensor[tensor : Except[_IndexArray], args__] := IndexTensor[IndexArray[tensor], IndexArray[args]]

IndexTensor[tensor_ ? IndexArrayQ, metric_ ? IndexArrayQ] := IndexTensor[tensor, {tensor["FreeIndexPositions"] -> metric}]


(* Index juggling *)

IndexContract[tensors : {__ ? IndexTensorQ}] := Enclose @ Block[{
	arrays, metrics, metricIndices, tensorIndices, contractions, reindexMetrics, reindex
},
	arrays = Through[tensors["IndexArray"]];
	metrics = Catenate[Through[tensors["Metrics"]]];
	metricIndices = Through[metrics["FreeIndices"]];
	tensorIndices = MapThread[
		If[#1["FreeQ"], {#1, #2, Replace[#2[[3]], Append[_ -> None] @ Thread[metrics[[#2[[1]]]]]]}, Nothing] &,
		{Catenate @ Through[tensors["FreeIndices"]], Catenate @ MapIndexed[Append[#2, #1] &, Through[tensors["FreeIndexPositions"]], {2}]}
	];
	contractions = Values[Take[#, 2] & /@ Select[GroupBy[tensorIndices, ({#[[1]]["Name"], Normal[#[[3]]]} &)], Length[#] > 1 &]];
	contractions = #[[All, ;; 2]] -> If[Equal @@ Through[#[[All, 1]]["Valence"]], #[[1, 3]], None] & /@ contractions;
	
	reindexMetrics = Map[
		With[{inverseQ = #[[1, 1, 1]]["LowerQ"], names = {Unique["i"], Unique["j"]}},
			MapThread[#1[[1]] -> #1[[2]] -> If[inverseQ, 1, -1] * #2 &, {#[[1, All, 2]], names}] ->
				If[inverseQ, Inverse[#[[2]]] @@ (- names), #[[2]] @@ names]
		] &,
		Cases[contractions, HoldPattern[_ -> _IndexArray]]
	];
	reindex = GroupBy[Catenate[reindexMetrics[[All, 1]]], First -> Last];
	Join[
		MapIndexed[
			With[{newIndex = Lookup[reindex, #2[[1]]]},
				If[MissingQ[newIndex], #1, #1 @@ newIndex]
			] &,
			arrays
		],
		reindexMetrics[[All, 2]]
	]
]

IndexContract[array_ ? IndexArrayQ, metrics_] := IndexContract[{array}, metrics]

IndexContract[arrays_List, metric_ ? IndexTensorQ] := IndexContract[arrays, metric["IndexArray"]]

IndexContract[arrays_List, metric_ ? IndexArrayQ] := IndexContract[IndexTensor[#, metric] & /@ arrays]

IndexContract[tensor_ ? IndexTensorQ] := IndexContract[{tensor}]


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

