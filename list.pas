type
  plist = ^list_node;
  list_node = record
    next: plist;
    value: integer;
  end;

function list_nil: plist;
begin
  list_nil := nil
end;

function list_is_nil(xs: plist): boolean;
begin
  list_is_nil := xs = nil
end;

function list_cons(v: integer; xs: plist): plist;
var
  n: plist;
begin
  New(n);
  n^.value := v;
  n^.next := xs;
  list_cons := n
end;

function list_head(xs: plist): integer;
begin
  list_head := xs^.value
end;

function list_tail(xs: plist): plist;
begin
  list_tail := xs^.next
end;

function list_len(xs: plist): integer;
var
  n: integer;
  p: plist;
begin
  n := 0;
  p := xs;
  while p <> nil do
  begin
    n := n + 1;
    p := p^.next
  end;
  list_len := n
end;

function list_reverse(xs: plist): plist;
var
  cur: plist;
  nxt: plist;
  outv: plist;
begin
  cur := xs;
  outv := nil;
  while cur <> nil do
  begin
    nxt := cur^.next;
    cur^.next := outv;
    outv := cur;
    cur := nxt
  end;
  list_reverse := outv
end;

procedure list_free(xs: plist);
var
  cur: plist;
  nxt: plist;
begin
  cur := xs;
  while cur <> nil do
  begin
    nxt := cur^.next;
    Dispose(cur);
    cur := nxt
  end
end;
