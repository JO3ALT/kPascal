program listpipelinedemo;
(* $I list.pas *)

procedure inc10(var src: integer; var dst: integer);
begin
  dst := src + 10
end;

function is_even(var v: integer): boolean;
begin
  is_even := (v mod 2) = 0
end;

function add_i(acc: integer; var v: integer): integer;
begin
  add_i := acc + v
end;

procedure print_list(xs: plist);
var
  p: plist;
begin
  p := xs;
  while p <> nil do
  begin
    WriteLn(p^.value);
    p := p^.next
  end
end;

procedure run_demo;
var
  xs: plist;
  ys: plist;
  zs: plist;
  s: integer;
begin

  xs := list_nil();
  xs := list_cons(5, xs);
  xs := list_cons(4, xs);
  xs := list_cons(3, xs);
  xs := list_cons(2, xs);
  xs := list_cons(1, xs);

  WriteLn(list_len(xs));
  WriteLn(list_head(xs));
  WriteLn(list_head(list_tail(xs)));

  ys := Map(xs, inc10);
  print_list(ys);

  zs := Filter(ys, is_even);
  WriteLn(list_len(zs));
  print_list(zs);

  s := Fold(zs, 0, add_i);
  WriteLn(s);

  list_free(zs);
  list_free(ys);
  list_free(xs)
end;

begin
  run_demo()
end.
