Package["WolframInstitute`Gravitas`IndexArray`"]

PackageExport[ShapeQ]
PackageExport[Shape]



ClearAll[ShapeQ, Shape, Prop]


(* Validation *)

ShapeQ[Shape[___Dimension ? DimensionQ]] := True

ShapeQ[___] := False


Shape[ds__Integer] := Shape @@ MapIndexed[Dimension[#1, DimensionName[#2[[1]]]] &, {ds}]

Shape[ds : {(_Integer | _Dimension) ...}] := Shape @@ ds

Shape[ds : {__Integer}, names_List] /; Length[ds] === Length[names] := With[{nameSigns = Replace[names, {- x_ :> {-1, x}, x_ :> {1, x}}, 1]},
    Shape @ MapThread[Dimension[#1 #2[[1]], #2[[2]]] &, {ds, nameSigns}]
]

Shape[names_List] := Shape[Dimension /@ names]

Shape[s_Shape] := s


(* Properties *)

(s_Shape ? ShapeQ)[prop_String, args___] := Prop[s, prop, args]

Prop[Shape[ds___], "Indices"] := {ds}

Prop[s_, "FreeIndices"] := Select[s["Indices"], #["FreeQ"] &]

Prop[s_, "SignedDimensions"] := Through[s["FreeIndices"]["SignedDimension"]]

Prop[s_, "Signs"] := Through[s["FreeIndices"]["Sign"]]

Prop[s_, "Dimensions"] := Through[s["FreeIndices"]["Dimension"]]

Prop[s_, "FreeIndexPositions"] := Select[s["Indices"], (#["FreeQ"] &) -> "Index"]

Prop[s_, "Dimension"] := Times @@ s["Dimensions"]

Prop[s_, "Rank"] := Length[s["FreeIndices"]]

Prop[s_, "Size"] := Length[s["Indices"]]

Prop[s_, "Variance"] := Thread[s["Signs"] == 1]

Prop[s_, "Names", alphabet_ : Automatic] :=
    MapIndexed[
        With[{
            name = #1["Name"], index = #1["Index"]
        },
            If[ MissingQ[index],
                If[name === None, DimensionName[#2[[1]], alphabet], name],
                #["IndexName"]
            ]
        ] &,
        s["Indices"]
    ]

Prop[_, prop_String, ___] := Missing[prop]


Shape["Properties"] = Sort @ Cases[DownValues[Prop], HoldPattern[_[Prop[_, prop_String, ___]] :> _] :> prop]



(* Formatting *)

Shape /: MakeBoxes[s_Shape ? ShapeQ, form_] := With[{
    box = ToBoxes[
        Row[
            MapThread[
                Tooltip[
                    DimensionSymbol[#1["Sign"], #2],
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

