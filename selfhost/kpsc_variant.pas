program kpsc_variant;
type
  node = record
    case tag: integer of
      0: (i: integer;);
      1: (j: integer; k: integer;);
  end;
var
  n: node;
begin
  n.tag := 1;
  n.j := 12;
  n.k := 30;
  WriteLn(n.j + n.k)
end.
