LoadPackage("IO");

create_file := function(n)
  local x,m,f,k,s,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  perms := Filtered(SymmetricGroup(n), x->not x=());	

  for k in perms do
    Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
    Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  od;

  lines := [ 
  "language ESSENCE' 1.0\n",
  Concatenation("letting n be ", String(n), "\n"),
  "letting perms be [", tmp1, "]\n",
  "letting inverses be [\n", tmp2, "]\n",
  "find M : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
  "such that\n",
  "forAll x,y : int(1..n) .", 
  "  M[M[x,y],x]=M[y,x],",
  ];

  Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ M[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,M[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

  Add(lines, "\ntrue\n");

  f := IO_File(Concatenation("strangeX", String(n), ".eprime"), "w");
  for x in lines do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
  
  return;
end;

read_file := function(n, filename)
  local l, k, x, m, f, done;
    
  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      k := k+1;
      Add(l, m);
    fi;
  od; 
  Print("I found ", k, " solutions\n");  
  return l;
end;

compute_strangeX := function(n)
  local m,l,T,k,s,f,x,t,input, output, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  k := 1;
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  create_file(n);

  output := Concatenation("strangeX", String(n));
  Print("Running savilerow. File: strangeX", String(n), ".eprime", ". Output: ", output, "\n");
  Exec(Concatenation(s, "strangeX", String(n), ".eprime", " >strangeX", String(n)));


  for x in read_file(n, output) do
    Add(t, x);
    m := m+1;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", m, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

  f := IO_File(Concatenation("Ssize", String(n), ".g"), "w");
  IO_WriteLine(f, Concatenation("Ssize", String(n), " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),",")); 
  od;

  IO_WriteLine(f, "];");
  IO_Flush(f);
  IO_Close(f);
end;

enumerate_strangeX := function(n)
  local m,l,T,k,s,f,x,done,output,t0,t1,mytime;

  t0 := NanosecondsSinceEpoch();

  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  create_file(n);

  LogTo();
  LogTo(Concatenation("strangeX", String(n), ".log"));

  output := Concatenation("strangeX", String(n));
  Print("Running savilerow. File: strangeX", String(n), ".eprime", ". Output: ", output, "\n");
  Exec(Concatenation(s, "strangeX", String(n), ".eprime", " >strangeX", String(n)));

  k := 0;
  f := IO_File(output, "r");

  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      k := k+1;
    fi;
  od; 

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I enumerated ", k, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

end;


