# This file produces the list of indecomposable cycle sets of size 10
# One needs to uncompress the files CSsize10_* in the 
# folder where this GAP script is located.

l := [];

for file in ["CSsize10_1",
  "CSsize10_10",
  "CSsize10_11",
  "CSsize10_12",
  "CSsize10_13",
  "CSsize10_14",
  "CSsize10_15",
  "CSsize10_16",
  "CSsize10_17",
  "CSsize10_18",
  "CSsize10_19",
  "CSsize10_2",
  "CSsize10_20",
  "CSsize10_21",
  "CSsize10_22",
  "CSsize10_23",
  "CSsize10_24",
  "CSsize10_25",
  "CSsize10_26",
  "CSsize10_27",
  "CSsize10_28",
  "CSsize10_29",
  "CSsize10_3",
  "CSsize10_30",
  "CSsize10_31",
  "CSsize10_32",
  "CSsize10_33",
  "CSsize10_34",
  "CSsize10_35",
  "CSsize10_36",
  "CSsize10_37",
  "CSsize10_38",
  "CSsize10_39",
  "CSsize10_4",
  "CSsize10_40",
  "CSsize10_41",
  "CSsize10_42",
  "CSsize10_5",
  "CSsize10_6",
  "CSsize10_7",
  "CSsize10_8",
  "CSsize10_9"] do
  Read(Concatenation(file, ".g"));
  for x in EvalString(file)  do
    cs := CycleSet(x);
    if IsIndecomposable(cs) then
      Add(l, cs);
    fi;
  od;
od;

