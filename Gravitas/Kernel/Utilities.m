Package["WolframInstitute`Gravitas`Utilities`"]

PackageExport[ToList]
PackageExport[FreshVariable]
PackageExport[CanonicalSymbolName]
PackageExport[SignedSymbolName]



ClearAll[ToList, FreshVariable, CanonicalSymbolName, SignedSymbolName]


ToList = Developer`ToList


FreshVariable[name_String] := Block[{$ModuleNumber = 1}, ToExpression[RowBox[{"Module", "[", "{", name, "}", ",", name, "]"}]]]


CanonicalSymbolName[s_Symbol ? AtomQ] := With[{t = Unevaluated @@ ResourceFunction["UnformalizeSymbols"][s, "DeferQ" -> True]}, SymbolName[t]]

CanonicalSymbolName[- s_] := CanonicalSymbolName[s]

CanonicalSymbolName[s_] := s


SignedSymbolName[- s_] := - SignedSymbolName[s]

SignedSymbolName[s_] := CanonicalSymbolName[s]

