LoadPackage("YangBaxter");

check_YB := function(m)
  local x, y, z, xy, xz, yx, yz, size;

  size := Size(m);

  ### Check (xy)(xz)=(yx)(yz)
  for x in [1..size] do
    for y in [x+1..size] do
      xy := m[x][y];
      yx := m[y][x];
      for z in [1..size] do
        xz := m[x][z];
        yz := m[y][z];
        if m[xy][xz] <> m[yx][yz] then
          Display([x,y,z]);
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

permutation_T := function(obj)
  local sigma;
  sigma := Permutations(obj);
  return PermList(List([1..Size(obj)], x->x^sigma[x]));
end;

all_Ts := function(n)
  return Set(List([1..NrSmallIYB(n)], x->permutation_T(SmallCycleSet(n,x))));
end;

count_withT := function(n, myT)
  return Number([1..NrSmallCycleSets(n)], x->permutation_T(SmallCycleSet(n,x))=myT);
end;

count_withT_uptoconjugation := function(n, myT)
  return Number([1..NrSmallCycleSets(n)], x->IsConjugate(SymmetricGroup(n),permutation_T(SmallCycleSet(n,x)),myT)=true);
end;

withT_uptoconjugation := function(n, myT)
  return Filtered([1..NrSmallCycleSets(n)], x->IsConjugate(SymmetricGroup(n),permutation_T(SmallCycleSet(n,x)),myT)=true);
end;

nr_sf := function(n)
  return Size(Filtered(List([1..NrSmallCycleSets(n)], x->SmallCycleSet(n,x)), IsSquareFree));
end;

twist_matrix := function(obj, f)
  local i,j,m,n,q;
  n := Size(obj);
  q := Inverse(f);
  m := NullMat(n,n);
  for i in [1..n] do
    for j in [1..n] do
      if obj[i^q][j^q] <> 0 then
        m[i][j] := obj[i^q][j^q]^f;
      fi;
    od;
  od;
  return m;
end;

partial_minimality := function(m, i, j, elements)
  local tmp, p, n;
  n := Size(m);
  for p in elements do
    tmp := Flat(twist_matrix(m, p));
    if not 0 in tmp{[1..n*(i-1)+j]} then
      if Flat(m){[1..n*(i-1)+j]} > tmp then
        return false;
      fi;
    fi;
  od;
  return true;
end;

is_minimal := function(m, centralizer)
  local p;
  for p in centralizer do
    if Flat(m) > Flat(twist_matrix(m, p)) then
      return false;
      fi;
  od;
  return true;
end;

# T=id nunca de conexo
# grupo abeliano, siempre es retractble (dos filas son iguales)
is_solvable := function(m, T)
  local perms;

  perms := Filtered(List(m, PermList), x->not x = fail);  
  if perms = [] then
    return true;
  else
    if T=() then
      if IsTransitive(Group(perms), [1..Size(m)]) then
        return false;
      fi;
    fi;
    return IsSolvable(Group(perms));
  fi;
end;

# This function checks whether (i.j).(i.k)=(j.i).(j.k) holds
# whenever it is possible
check_condition := function(m, i, j, k)
  local ij, ik, ji, jk;
  
  ij := m[i][j];
  ji := m[j][i];
  ik := m[i][k];
  jk := m[j][k];

  # (i.j).(i.k) = (j.i).(j.k)
  if ik*jk*ij*ji <> 0 then 
    if not m[ij][ik]*m[ji][jk]=0 then
      if not m[ij][ik] = m[ji][jk] then
        return false;
      fi;
    fi;
  fi;
  return true;
end;

tau_y := function(m, y, x)
  return Position(m[y], x);
end;

new_check := function(m, i, j)
  local t;
  t := tau_y(m, j, i);
  if not t = fail then
    if not m[i][m[j][j]]*m[t][j] = 0 then
      if not m[i][m[j][j]] = m[m[t][j]][m[t][j]] then
        return false;
      fi;
    fi;
  fi;
  return true;
end;

# Each y->x.y is invertible
# (x.y).(x.z)=(y.x).(y.z)
is_cycleset := function(m, i, j, T)
  local f,k,n,t,perms;

 # if i = j then
 #   return true;
 # fi;

  # (i.j).(i.i)=(j.i).(j.i)
  if not check_condition(m, i, j, i) then
    return false;
  fi;

  # (i.j).(i.j)=(j.i).(j.j)
  if not check_condition(m, i, j, j) then
    return false;
  fi;

  n := Size(m);

  for k in [1..n] do
    f := Filtered(m[k], x->not x = 0);
    if not Size(f) = Size(Collected(f)) then
      return false;
    fi;
  od;

  for k in [1..n] do

    if k=i or k=j then
      continue;
    fi;

    # (i.j).(i.k) = (j.i).(j.k)
    if not check_condition(m, i, j, k) then
      return false;
    fi;

    # (i.k).(i.i) = (k.i).(k.i)
    if not check_condition(m, i, k, i) then
      return false;
    fi;

    # (i.k).(i.j) = (k.i).(k.j)
    if not check_condition(m, i, k, j) then
      return false;
    fi;

    # (i.k).(i.k) = (k.i).(k.k)
    if not check_condition(m, i, k, k) then
      return false;
    fi;

    # (j.k).(j.i) = (k.j).(k.i)
    if not check_condition(m, j, k, i) then
      return false;
    fi;

    # (j.k).(j.j) = (k.j).(k.j)
    if not check_condition(m, j, k, j) then
      return false;
    fi;

    # (j.k).(j.k) = (k.j).(k.k)
    if not check_condition(m, j, k, k) then
      return false;
    fi;

  od;
  return true;
end;

construct_withT := function(n, T)
  local f, m, p, k, i, j, l, c, elements, done, x;

  m := NullMat(n,n);
  p := ListPerm(T, n);
  
  for k in [1..n] do
    m[k][k] := p[k];
  od;

  i := 1;
  j := 2;

  k := 0;
  l := [];
  
  c := Centralizer(SymmetricGroup(n), T);
  if T=() then
    elements := List([1..n-1], x->(x,x+1));
  else
    elements := GeneratorsOfGroup(c);
  fi;

  done := false;
  
  while not done do
  
    for x in [1..n] do
      m[i][j] := m[i][j]+1;
      if not m[i][j] in m[i]{[1..j-1]} then
        break;
      fi;
    od;
  
    if m[i][j] > n then
      if [i,j]=[1,2] then 
        Print("I found ", k, " solutions with T=", T, ".\n"); 
        done := true;
      else
        m[i][j] := 0;
        if j=1 then 
          i := i-1;
          j := n;
        else
          j := j-1;
          if i = j then
            j := j-1;
          fi;
        fi;
      fi;
    else
      if is_cycleset(m,i,j,T) then
        if partial_minimality(m,i,j,elements) then 
          if [i,j]=[n,n-1] then
            if is_minimal(m,c) then 
              if check_YB(m) then
                Add(l, StructuralCopy(m));
                k := k+1;
              else
                Display(m);
              fi;
            fi;
          else
            if j = n then 
              if is_solvable(m, T) then
                i := i+1;
                j := 1;
              fi;
            else
              j := j+1;
              if i=j then
                j := j+1;
              fi;
            fi;
          fi;
        fi;
      fi;
    fi;
  od;;

  return l;
end;

construct := function(n)
  local k,l,c,x,t,tmp, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  LogTo();
  LogTo(Concatenation("size", String(n), ".log"));

  l := [];
  k := 0;

  for c in Reversed(List(ConjugacyClasses(SymmetricGroup(n)), Representative)) do
    tmp := StructuralCopy(construct_withT(n, c));
    k := k+Size(tmp);
    for x in tmp do
      Add(l, StructuralCopy(x));
    od;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", k, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

  return l;

end;

