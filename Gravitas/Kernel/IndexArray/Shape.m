Package["WolframInstitute`Gravitas`IndexArray`"]

PackageExport[ShapeQ]
PackageExport[Shape]



ClearAll[ShapeQ, Shape, Prop]


(* Validation *)

ShapeQ[Shape[___Dimension ? DimensionQ]] := True

ShapeQ[___] := False


Shape[ds__Integer] := Shape @@ MapIndexed[Dimension[#1, DimensionName[#2[[1]]]] &, {ds}]

Shape[ds : {(_Integer | _Dimension) ...}] := Shape @@ ds

Shape[s_Shape] := s


Shape["Properties"] = Sort @ {
    "Indices", "SignedDimensions", "Dimensions", "Rank", "Size", "Variance", "Names",
    "Properties"
}

(s_Shape ? ShapeQ)[prop_String, args___] := Prop[s, prop, args]

Prop[Shape[ds___], "Indices"] := {ds}

Prop[s_, "SignedDimensions"] := If[#["IndexQ"], Nothing, #["SignedDimension"]] & /@ s["Indices"]

Prop[s_, "Dimensions"] := Abs[s["SignedDimensions"]]

Prop[s_, "Rank"] := Length[s["SignedDimensions"]]

Prop[s_, "Size"] := Length[s["Indices"]]

Prop[s_, "Variance"] := Thread[s["SignedDimensions"] > 0]

Prop[s_, "Names", alphabet_ : Automatic] :=
    MapIndexed[With[{name = #1["Name"], index = #1["Index"]}, If[MissingQ[index], If[name === None, DimensionName[#2[[1]], alphabet], name], index]] &, s["Indices"]]

Prop[_, prop_String, ___] := Missing[prop]

Shape /: MakeBoxes[s_Shape ? ShapeQ, form_] := With[{
    box = ToBoxes[
        Row[
            MapThread[
                Tooltip[
                    DimensionSymbol[#1["SignedDimension"], #2],
                    #1["View"]
                ] &,
                {s["Indices"], s["Names"]}
            ]
        ],
        form
    ]
},
    InterpretationBox[box, s]
]