Package["WolframInstitute`Gravitas`IndexArray`"]

PackageImport["WolframInstitute`Gravitas`Utilities`"]

PackageExport[DimensionQ]
PackageExport[Dimension]

PackageScope[DimensionName]
PackageScope[DimensionSymbol]



ClearAll[DimensionQ, Dimension, DimensionName, Prop]

(* Validation *)

DimensionName[i_Integer ? Positive, alphabet : {__}] := Block[{
    n = Length[alphabet],
    j, k
}, 
    j = Mod[i - 1, n] + 1;
    k = Quotient[i - 1, n];
    ToString[alphabet[[j]]] <> If[k > 0, ToString[k], ""]
]

DimensionName[i_, Automatic] := DimensionName[i, CharacterRange["i", "z"]]

DimensionName[i_] := DimensionName[i, Automatic]




DimensionQ[Dimension[_Integer, _, Except[_List], ___]] := False

DimensionQ[Dimension[_Integer, _, _, Except[_Integer], ___]] := False

DimensionQ[Dimension[_Integer, ___]] := True

DimensionQ[___] := False



Dimension[Dimension[d_, name_, indices_List : {}, _ : None, args___] ? DimensionQ, index_Integer] := Dimension[d, name, indices, index, args]

Dimension[Dimension[d_, name_, _, args___] ? DimensionQ, indices_List] := Dimension[d, name, indices, args]

Dimension[Dimension[d_, name_, args___] ? DimensionQ, newName_, newArgs___] := Dimension[d, Replace[newName, All | Inherited -> name], newArgs, ##] & @@ Drop[{args}, UpTo[Length[{newArgs}]]]

Dimension[d_Dimension ? DimensionQ] := d


Dimension["Properties"] = Sort @ {
    "SignedDimension", "Dimension", "Size", "Name", "SignedName", "Indices", "Index", "IndexName", "FreeQ",
    "Properties"
}

(d_Dimension ? DimensionQ)[prop_String, args___] := Prop[d, prop, args]

Prop[d : Dimension[n_, ___], "SignedDimension"] := With[{index = d["Index"]}, If[! MissingQ[index] && IntegerQ[index] && 0 < index <= Abs[n], Sign[n], n]]

Prop[d_, "Dimension" | "Size"] := Abs[d["SignedDimension"]]

Prop[d_, "Variance" | "Sign"] := Sign[d["SignedDimension"]]

Prop[Dimension[_, name_, ___], "Name"] := CanonicalSymbolName[name]

Prop[_, "Name"] := None

Prop[d_, "SignedName"] := d["Sign"] * d["Name"]

Prop[Dimension[n_, args___], "Lower"] := Dimension[- Abs[n], args]

Prop[Dimension[n_, args___], "Upper"] := Dimension[Abs[n], args]

Prop[Dimension[n_, args___], "Minus" | "Toggle"] := Dimension[- n, args]

Prop[d_, "LowerQ"] := d["Sign"] < 0

Prop[d_, "UpperQ"] := d["Sign"] >= 0

Prop[Dimension[n_, name_ : "i", indices : {___} : {}, ___], "Indices"] := indices
    (* Take[Join[indices, Array[Subscript[name, #] &, Max[0, Abs[n] - Length[indices]], Length[indices] + 1]], UpTo[Abs[n]]] *)

Prop[Dimension[_, _, _, index_, ___], "Index"] := index

Prop[_, "Index"] := Missing["Index"]

Prop[d_, "FreeQ"] := MissingQ[d["Index"]]

DimensionSymbol[d_, name_] :=
    Which[d > 0, OverBar[name], d < 0, UnderBar[name], True, Style[name, Opacity[.3]]]

Prop[d_, "IndexName"] := With[{index = d["Index"], indices = d["Indices"]},
    If[MissingQ[index], d["Name"], If[IntegerQ[index] && 0 < index <= Length[indices], indices[[index]], index]]
]

Prop[d_, "Symbol"] := DimensionSymbol[d["SignedDimension"], d["IndexName"]]

Prop[d_, "View", limit_Integer : 10] := With[{dim = d["Dimension"]},
    If[dim > limit, dim, Row[{dim, " : ", Row[d["Indices"], ","]}]]
]


Prop[_, prop_String, ___] := Missing[prop]


(* UpValues *)

Dimension /: - (d_Dimension ? DimensionQ) := d["Minus"]

Dimension /: Equal[ds__Dimension ? DimensionQ] := SameQ @@ Through[{ds}["Indices"]]


(* Formatting *)

Dimension /: MakeBoxes[d_Dimension ? DimensionQ, form_] := With[{
    box = ToBoxes[d["Symbol"], form],
    tooltip = ToBoxes[d["View"], form]
},
    InterpretationBox[box, d, Tooltip -> tooltip]
]

