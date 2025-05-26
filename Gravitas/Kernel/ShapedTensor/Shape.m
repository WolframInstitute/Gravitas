Package["WolframInstitute`Gravitas`ShapedTensor`"]

PackageExport[ShapeQ]
PackageExport[Shape]



ClearAll[ShapeQ, Shape, Prop]


(* Validation *)

ShapeQ[Shape[___Dimension ? DimensionQ]] := True

ShapeQ[___] := False


Shape[] := Shape[Dimension[1]]

Shape[ds___Integer] := Shape @@ MapIndexed[Dimension[#1, DimensionName[#2[[1]]]] &, {ds}]

Shape[ds : {___Integer}] := Shape @@ ds

Shape[s_Shape] := s


Shape["Properties"] = Sort @ {
    "Indices", "SignedDimensions", "Dimensions", "Rank", "Variance", "Names",
    "Properties"
}

(s_Shape ? ShapeQ)[prop_String, args___] := Prop[s, prop, args]

Prop[Shape[ds___], "Indices"] := {ds}

Prop[s_, "SignedDimensions"] := Through[s["Indices"]["SignedDimension"]]

Prop[s_, "Dimensions"] := Abs[s["SignedDimensions"]]

Prop[s_, "Rank"] := Length[s["Indices"]]

Prop[s_, "Variance"] := Thread[s["SignedDimensions"] < 0]

Prop[s_, "Names", alphabet_ : Automatic] :=
    MapIndexed[Replace[#1, {Dimension[_, name_, ___] :> name, _ :> DimensionName[#2[[1]], alphabet]}] &, s["Indices"]]

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