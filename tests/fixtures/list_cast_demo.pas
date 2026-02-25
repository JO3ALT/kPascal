program listcastdemo;
(* $I list.pas *)

procedure inc1(var src: integer; var dst: integer);
begin
  dst := src + 1
end;

function ge4(var v: integer): boolean;
begin
  ge4 := v >= 4
end;

function add_i(acc: integer; var v: integer): integer;
begin
  add_i := acc + v
end;

procedure run_demo;
type
  plist2 = ^list_node2;
  list_node2 = record
    next: plist2;
    value: integer;
  end;
var
  xs2: plist2;
  ys2: plist2;
  zs2: plist2;
  tmp: plist;
  s: integer;
  p: plist2;
begin
  xs2 := nil;
  xs2 := cast(plist2, list_cons(1, cast(plist, xs2)));
  xs2 := cast(plist2, list_cons(2, cast(plist, xs2)));
  xs2 := cast(plist2, list_cons(3, cast(plist, xs2)));
  xs2 := cast(plist2, list_cons(4, cast(plist, xs2)));

  WriteLn(list_len(cast(plist, xs2)));
  WriteLn(xs2^.value);
  WriteLn(xs2^.next^.value);

  tmp := Map(cast(plist, xs2), inc1);
  ys2 := cast(plist2, tmp);
  p := ys2;
  while p <> nil do
  begin
    WriteLn(p^.value);
    p := p^.next
  end;

  tmp := Filter(cast(plist, ys2), ge4);
  zs2 := cast(plist2, tmp);
  WriteLn(list_len(cast(plist, zs2)));
  p := zs2;
  while p <> nil do
  begin
    WriteLn(p^.value);
    p := p^.next
  end;

  s := Fold(cast(plist, zs2), 0, add_i);
  WriteLn(s);

  list_free(cast(plist, zs2));
  list_free(cast(plist, ys2));
  list_free(cast(plist, xs2))
end;

begin
  run_demo()
end.
