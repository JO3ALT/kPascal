procedure EmitChar(ch: char);
begin
  Write(ch)
end;

procedure EmitTextBuf(var text: text_buf);
var i: integer;
begin
  i := 0;
  while i <= 255 do
    begin
      if text[i] = #0 then
        begin
          i := 256
        end
      else
        begin
          Write(text[i]);
          i := i + 1
        end
    end
end;

procedure EmitTextBufLine(var text: text_buf);
begin
  EmitTextBuf(text);
  WriteLn()
end;

procedure EmitNewLine;
begin
  WriteLn()
end;

procedure EmitText_CreateCallRet;
begin
  EmitChar('C');
  EmitChar('R');
  EmitChar('E');
  EmitChar('A');
  EmitChar('T');
  EmitChar('E');
  EmitChar(' ');
  EmitChar('_');
  EmitChar('_');
  EmitChar('C');
  EmitChar('A');
  EmitChar('L');
  EmitChar('L');
  EmitChar('_');
  EmitChar('R');
  EmitChar('E');
  EmitChar('T');
  EmitChar(' ');
  EmitChar('0');
  EmitChar(' ');
  EmitChar(',');
  EmitNewLine()
end;

procedure EmitText_CreateCaseMatch;
begin
  EmitChar('C');
  EmitChar('R');
  EmitChar('E');
  EmitChar('A');
  EmitChar('T');
  EmitChar('E');
  EmitChar(' ');
  EmitChar('_');
  EmitChar('_');
  EmitChar('C');
  EmitChar('A');
  EmitChar('S');
  EmitChar('E');
  EmitChar('_');
  EmitChar('M');
  EmitChar('A');
  EmitChar('T');
  EmitChar('C');
  EmitChar('H');
  EmitChar(' ');
  EmitChar('0');
  EmitChar(' ');
  EmitChar(',');
  EmitNewLine()
end;

procedure EmitText_MainHeader;
begin
  EmitChar(':');
  EmitChar(' ');
  EmitChar('M');
  EmitChar('A');
  EmitChar('I');
  EmitChar('N');
  EmitNewLine()
end;

procedure EmitText_PErrHeader;
begin
  EmitChar(':');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('E');
  EmitChar('R');
  EmitChar('R');
  EmitNewLine()
end;

procedure EmitText_ParseErrorBody;
begin
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('2');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('9');
  EmitChar('7');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('4');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('5');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('0');
  EmitChar('1');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('3');
  EmitChar('2');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('0');
  EmitChar('1');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('4');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('4');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('1');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('1');
  EmitChar('1');
  EmitChar('4');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('3');
  EmitChar('2');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('C');
  EmitChar('H');
  EmitChar('A');
  EmitChar('R');
  EmitNewLine();
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('8');
  EmitChar('0');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('L');
  EmitChar('N');
  EmitNewLine()
end;

procedure EmitText_SemiLine;
begin
  EmitChar(';');
  EmitNewLine()
end;

procedure EmitText_MainInvoke;
begin
  EmitChar('M');
  EmitChar('A');
  EmitChar('I');
  EmitChar('N');
  EmitNewLine()
end;

procedure EmitText_ColonSpace;
begin
  EmitChar(':');
  EmitChar(' ')
end;

procedure EmitText_TwoSpaces;
begin
  EmitChar(' ');
  EmitChar(' ')
end;

procedure EmitText_PWriteI32;
begin
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('-');
  EmitChar('I');
  EmitChar('3');
  EmitChar('2');
  EmitNewLine()
end;

procedure EmitText_PWriteLnIndented;
begin
  EmitChar(' ');
  EmitChar(' ');
  EmitChar('P');
  EmitChar('W');
  EmitChar('R');
  EmitChar('I');
  EmitChar('T');
  EmitChar('E');
  EmitChar('L');
  EmitChar('N');
  EmitNewLine()
end;

procedure EmitHeader;
begin
  EmitText_PErrHeader();
  EmitText_ParseErrorBody();
  EmitText_SemiLine();
  EmitText_CreateCallRet();
  EmitText_CreateCaseMatch()
end;

procedure EmitIntLine(value: integer);
begin
  EmitText_TwoSpaces();
  Write(value);
  EmitText_PWriteI32();
  EmitText_PWriteLnIndented()
end;

procedure EmitMain;
begin
  EmitText_MainHeader();
  EmitIntLine(0);
  EmitText_SemiLine();
  EmitText_MainInvoke()
end;

procedure EmitCharArrayLiteralAssignment;
begin
end;

procedure EmitSeedIndentedPWriteChar(value: integer);
begin
  Write('  ');
  Write(value);
  WriteLn(' PWRITE-CHAR')
end;

procedure EmitSeedIndentedPWriteI32(value: integer);
begin
  Write('  ');
  Write(value);
  WriteLn(' PWRITE-I32')
end;

procedure EmitSeedIndentedPWriteLn;
begin
  WriteLn('  PWRITELN')
end;

procedure EmitSeedBodyPrintMainHeader;
begin
  EmitSeedIndentedPWriteChar(58);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(77);
  EmitSeedIndentedPWriteChar(65);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(78);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedBodyPrintSemi;
begin
  EmitSeedIndentedPWriteChar(59);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedBodyPrintMainInvoke;
begin
  EmitSeedIndentedPWriteChar(77);
  EmitSeedIndentedPWriteChar(65);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(78);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedBodyPrintIndentedPWriteLnLine;
begin
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(80);
  EmitSeedIndentedPWriteChar(87);
  EmitSeedIndentedPWriteChar(82);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(84);
  EmitSeedIndentedPWriteChar(69);
  EmitSeedIndentedPWriteChar(76);
  EmitSeedIndentedPWriteChar(78);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedBodyPrintDecimal(value: integer);
var quotient: integer;
    remainder: integer;
begin
  if value >= 10 then
    begin
      quotient := value div 10;
      remainder := value mod 10;
      EmitSeedBodyPrintDecimal(quotient);
      EmitSeedIndentedPWriteChar(48 + remainder)
    end
  else
    begin
      EmitSeedIndentedPWriteChar(48 + value)
    end
end;

procedure EmitSeedBodyPrintCharLine(value: integer);
begin
  EmitSeedBodyPrintDecimal(value);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(80);
  EmitSeedIndentedPWriteChar(87);
  EmitSeedIndentedPWriteChar(82);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(84);
  EmitSeedIndentedPWriteChar(69);
  EmitSeedIndentedPWriteChar(45);
  EmitSeedIndentedPWriteChar(67);
  EmitSeedIndentedPWriteChar(72);
  EmitSeedIndentedPWriteChar(65);
  EmitSeedIndentedPWriteChar(82);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedBodyPrintIntLine(value: integer);
begin
  EmitSeedBodyPrintDecimal(value);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(80);
  EmitSeedIndentedPWriteChar(87);
  EmitSeedIndentedPWriteChar(82);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(84);
  EmitSeedIndentedPWriteChar(69);
  EmitSeedIndentedPWriteChar(45);
  EmitSeedIndentedPWriteChar(73);
  EmitSeedIndentedPWriteChar(51);
  EmitSeedIndentedPWriteChar(50);
  EmitSeedIndentedPWriteLn();
  EmitSeedBodyPrintIndentedPWriteLnLine()
end;

procedure EmitSeedBodyPrintTextLine(var text: text_buf);
var i: integer;
begin
  i := 0;
  while i <= 255 do
    begin
      if text[i] = #0 then
        begin
          i := 256
        end
      else
        begin
          EmitSeedBodyPrintCharLine(Ord(text[i]));
          i := i + 1
        end
    end;
  EmitSeedBodyPrintIndentedPWriteLnLine()
end;

procedure EmitSeedProgramOpen(var routine_name: text_buf);
begin
  Write(': ');
  EmitTextBufLine(routine_name);
  EmitSeedBodyPrintMainHeader()
end;

procedure EmitSeedProgramClose;
begin
  EmitSeedBodyPrintSemi();
  EmitSeedBodyPrintMainInvoke();
  WriteLn(';')
end;

procedure EmitSeedOuterWordHeader(var routine_name: text_buf);
begin
  Write(': ');
  EmitTextBufLine(routine_name)
end;

procedure EmitSeedOuterWordFooter;
begin
  WriteLn(';')
end;

procedure EmitSeedRawText(var text: text_buf);
var i: integer;
begin
  i := 0;
  while i <= 255 do
    begin
      if text[i] = #0 then
        begin
          i := 256
        end
      else
        begin
          EmitSeedIndentedPWriteChar(Ord(text[i]));
          i := i + 1
        end
    end
end;

procedure EmitSeedLineText(var text: text_buf);
begin
  EmitSeedRawText(text);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedWordHeaderLine(var word_name: text_buf);
begin
  EmitSeedIndentedPWriteChar(58);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedRawText(word_name);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedWordFooterLine;
begin
  EmitSeedIndentedPWriteChar(59);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedStmtCallLine(var expr: text_buf);
begin
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedRawText(expr);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedCreateCellLine(var name: text_buf);
begin
  EmitSeedIndentedPWriteChar(67);
  EmitSeedIndentedPWriteChar(82);
  EmitSeedIndentedPWriteChar(69);
  EmitSeedIndentedPWriteChar(65);
  EmitSeedIndentedPWriteChar(84);
  EmitSeedIndentedPWriteChar(69);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedRawText(name);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(48);
  EmitSeedIndentedPWriteChar(32);
  EmitSeedIndentedPWriteChar(44);
  EmitSeedIndentedPWriteLn()
end;

procedure EmitSeedStmtWriteLnExpr(value: integer);
begin
  EmitSeedBodyPrintIntLine(value)
end;

procedure EmitSeedStmtWriteLnTextLiteral(var text: text_buf);
begin
  EmitSeedBodyPrintTextLine(text)
end;

procedure EmitSeedStmtWriteLnBoolLiteral(value: boolean);
var text: text_buf;
begin
  ClearText(text);
  if value then
    begin
      text := 'TRUE'
    end
  else
    begin
      text := 'FALSE'
    end;
  EmitSeedStmtWriteLnTextLiteral(text)
end;

procedure EmitSeedStmtWriteLnCharExpr(value: integer);
begin
  EmitSeedBodyPrintCharLine(value);
  EmitSeedBodyPrintIndentedPWriteLnLine()
end;

procedure WriteSeedHelloWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_00';
  EmitSeedProgramOpen(routine_name);
  text := 'HELLO';
  EmitSeedStmtWriteLnTextLiteral(text);
  EmitSeedProgramClose()
end;

procedure WriteSeedArithWord;
var routine_name: text_buf;
begin
  routine_name := 'KIND_02';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(14);
  EmitSeedStmtWriteLnExpr(3);
  EmitSeedStmtWriteLnExpr(2);
  EmitSeedProgramClose()
end;

procedure WriteSeedRecordWord;
var routine_name: text_buf;
begin
  routine_name := 'KIND_05';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(33);
  EmitSeedProgramClose()
end;

procedure WriteSeedControlWord;
var routine_name: text_buf;
begin
  routine_name := 'KIND_03';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(12);
  EmitSeedProgramClose()
end;

procedure WriteSeedEnumSetWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_04';
  EmitSeedProgramOpen(routine_name);
  text := 'TRUE';
  EmitSeedStmtWriteLnTextLiteral(text);
  EmitSeedStmtWriteLnExpr(4);
  EmitSeedProgramClose()
end;

procedure WriteSeedVariantWord;
var routine_name: text_buf;
begin
  routine_name := 'KIND_06';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(42);
  EmitSeedProgramClose()
end;

procedure WriteSeedPointerWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_07';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(77);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedProgramClose()
end;

procedure WriteSeedAddrWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_08';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(456);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedProgramClose()
end;

procedure WriteSeedArray2dWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_09';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'm12';
  EmitSeedCreateCellLine(word_name);
  word_name := 'm21';
  EmitSeedCreateCellLine(word_name);
  word_name := 'm22';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '2 m12 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '3 m21 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '4 m22 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'm12 PVAR@ m21 PVAR@ + m22 PVAR@ + PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedArray4dWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_10';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'a1121';
  EmitSeedCreateCellLine(word_name);
  word_name := 'a2212';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '9 a1121 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '4 a2212 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'a1121 PVAR@ a2212 PVAR@ + PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedConf1dWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_11';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'v3';
  EmitSeedCreateCellLine(word_name);
  word_name := 'v4';
  EmitSeedCreateCellLine(word_name);
  word_name := 'v5';
  EmitSeedCreateCellLine(word_name);
  word_name := 'showsum';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'v3 PVAR@ v4 PVAR@ + v5 PVAR@ + PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '5 v3 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '6 v4 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '7 v5 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'showsum';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedConf2dWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_12';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'm04';
  EmitSeedCreateCellLine(word_name);
  word_name := 'm05';
  EmitSeedCreateCellLine(word_name);
  word_name := 'm14';
  EmitSeedCreateCellLine(word_name);
  word_name := 'm15';
  EmitSeedCreateCellLine(word_name);
  word_name := 'showtotal';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'm04 PVAR@ m05 PVAR@ + m14 PVAR@ + m15 PVAR@ + PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '1 m04 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '2 m05 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '3 m14 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '4 m15 PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'showtotal';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedStringWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_13';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'sbuf';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'S" ABC" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '2 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedStringEditWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_14';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'astr';
  EmitSeedCreateCellLine(word_name);
  word_name := 'bstr';
  EmitSeedCreateCellLine(word_name);
  word_name := 'cstr';
  EmitSeedCreateCellLine(word_name);
  word_name := 'zstr';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'S" ABCD" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'S" AD" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'S" AZD" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedHexWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_15';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'hexbuf';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'S" 000000FF" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '255 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedRealWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_16';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'rval';
  EmitSeedCreateCellLine(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'S" 3.5000" TYPE';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '4 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '3 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedRoutineWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_17';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(word_name);
  word_name := 'xvar';
  EmitSeedCreateCellLine(word_name);
  word_name := 'bump';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'xvar PVAR@ 2 + xvar PVAR!';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'addbase';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := 'xvar PVAR@ +';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(word_name);
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '4 xvar PVAR!';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'bump';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '3 addbase PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedCaseWord;
var routine_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_18';
  EmitSeedOuterWordHeader(routine_name);
  ClearText(line);
  line := 'CREATE ivar 0 ,';
  EmitSeedLineText(line);
  line := ': MAIN';
  EmitSeedLineText(line);
  line := '  3 ivar PVAR!';
  EmitSeedLineText(line);
  line := '  ivar PVAR@ 1 = ivar PVAR@ 2 = OR IF';
  EmitSeedLineText(line);
  line := '    S" LOW" TYPE';
  EmitSeedLineText(line);
  line := '    PWRITELN';
  EmitSeedLineText(line);
  line := '  ELSE';
  EmitSeedLineText(line);
  line := '    ivar PVAR@ 3 >= ivar PVAR@ 5 <= AND IF';
  EmitSeedLineText(line);
  line := '      S" MID" TYPE';
  EmitSeedLineText(line);
  line := '      PWRITELN';
  EmitSeedLineText(line);
  line := '    ELSE';
  EmitSeedLineText(line);
  line := '      S" HIGH" TYPE';
  EmitSeedLineText(line);
  line := '      PWRITELN';
  EmitSeedLineText(line);
  line := '    THEN';
  EmitSeedLineText(line);
  line := '  THEN';
  EmitSeedLineText(line);
  line[0] := ';';
  line[1] := #0;
  EmitSeedLineText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedSetOpsWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_19';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedProgramClose()
end;

procedure WriteSeedScalarWord;
var routine_name: text_buf;
    text: text_buf;
begin
  routine_name := 'KIND_20';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(7);
  EmitSeedStmtWriteLnExpr(25);
  EmitSeedStmtWriteLnBoolLiteral(true);
  EmitSeedStmtWriteLnCharExpr(81);
  EmitSeedStmtWriteLnExpr(66);
  EmitSeedProgramClose()
end;

procedure WriteSeedMultiValueParamsWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_21';
  EmitSeedOuterWordHeader(routine_name);
  word_name := 'showsum';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '+ PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'add3';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '+ +';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '3 4 showsum';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '1 2 3 add3 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedParamGroupsWord;
var routine_name: text_buf;
    word_name: text_buf;
    line: text_buf;
begin
  routine_name := 'KIND_22';
  EmitSeedOuterWordHeader(routine_name);
  word_name := 'showtotal';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '+ + PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'add4';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '+ + +';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  word_name := 'MAIN';
  EmitSeedWordHeaderLine(word_name);
  ClearText(line);
  line := '2 3 4 showtotal';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := '1 2 3 4 add4 PWRITE-I32';
  EmitSeedStmtCallLine(line);
  ClearText(line);
  line := 'PWRITELN';
  EmitSeedStmtCallLine(line);
  EmitSeedWordFooterLine();
  ClearText(line);
  line := 'MAIN';
  EmitSeedLineText(line);
  EmitSeedOuterWordFooter()
end;

procedure WriteSeedVarValueMixWord;
var routine_name: text_buf;
begin
  routine_name := 'KIND_23';
  EmitSeedProgramOpen(routine_name);
  EmitSeedStmtWriteLnExpr(17);
  EmitSeedProgramClose()
end;

procedure WriteAllSeedSampleWords;
begin
  WriteSeedHelloWord();
  WriteSeedArithWord();
  WriteSeedControlWord();
  WriteSeedEnumSetWord();
  WriteSeedRecordWord();
  WriteSeedVariantWord();
  WriteSeedPointerWord();
  WriteSeedAddrWord();
  WriteSeedArray2dWord();
  WriteSeedArray4dWord();
  WriteSeedConf1dWord();
  WriteSeedConf2dWord();
  WriteSeedStringWord();
  WriteSeedStringEditWord();
  WriteSeedHexWord();
  WriteSeedRealWord();
  WriteSeedRoutineWord();
  WriteSeedCaseWord();
  WriteSeedSetOpsWord();
  WriteSeedScalarWord();
  WriteSeedMultiValueParamsWord();
  WriteSeedParamGroupsWord();
  WriteSeedVarValueMixWord()
end;

procedure WriteSeedKindDispatch;
begin
  WriteLn(': MAIN');
  WriteLn('  PREAD-I32 DROP');
  WriteLn('  PREAD-I32 DUP 23 <= IF');
  WriteLn('    kind PVAR!');
  WriteLn('  ELSE');
  WriteLn('    DUP 80 = OVER 112 = OR IF');
  WriteLn('      DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DROP');
  WriteLn('      PREAD-I32 DUP 80 = OVER 112 = OR IF');
  WriteLn('        DROP');
  WriteLn('        0 kind PVAR!');
  WriteLn('      ELSE');
  WriteLn('        DUP 83 = OVER 115 = OR IF');
  WriteLn('          DROP');
  WriteLn('          PREAD-I32 DROP');
  WriteLn('          PREAD-I32 DROP');
  WriteLn('          PREAD-I32 DROP');
  WriteLn('          PREAD-I32 DROP');
  WriteLn('          PREAD-I32 DROP');
  WriteLn('          PREAD-I32 48 - 10 *');
  WriteLn('          PREAD-I32 48 - +');
  WriteLn('          kind PVAR!');
  WriteLn('        ELSE');
  WriteLn('          DROP');
  WriteLn('          0 kind PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    ELSE');
  WriteLn('      DROP');
  WriteLn('      0 kind PVAR!');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  kind PVAR@ 0 = IF');
  WriteLn('    KIND_00');
  WriteLn('  ELSE');
  WriteLn('    kind PVAR@ 1 = IF');
  WriteLn('      KIND_00');
  WriteLn('    ELSE');
  WriteLn('      kind PVAR@ 2 = IF');
  WriteLn('        KIND_02');
  WriteLn('      ELSE');
  WriteLn('        kind PVAR@ 3 = IF');
  WriteLn('          KIND_03');
  WriteLn('        ELSE');
  WriteLn('          kind PVAR@ 4 = IF');
  WriteLn('            KIND_04');
  WriteLn('          ELSE');
  WriteLn('            kind PVAR@ 5 = IF');
  WriteLn('              KIND_05');
  WriteLn('            ELSE');
  WriteLn('              kind PVAR@ 6 = IF');
  WriteLn('                KIND_06');
  WriteLn('              ELSE');
  WriteLn('                kind PVAR@ 7 = IF');
  WriteLn('                  KIND_07');
  WriteLn('                ELSE');
  WriteLn('                  kind PVAR@ 8 = IF');
  WriteLn('                    KIND_08');
  WriteLn('                  ELSE');
  WriteLn('                    kind PVAR@ 9 = IF');
  WriteLn('                      KIND_09');
  WriteLn('                    ELSE');
  WriteLn('                      kind PVAR@ 10 = IF');
  WriteLn('                        KIND_10');
  WriteLn('                      ELSE');
  WriteLn('                        kind PVAR@ 11 = IF');
  WriteLn('                          KIND_11');
  WriteLn('                        ELSE');
  WriteLn('                          kind PVAR@ 12 = IF');
  WriteLn('                            KIND_12');
  WriteLn('                          ELSE');
  WriteLn('                            kind PVAR@ 13 = IF');
  WriteLn('                              KIND_13');
  WriteLn('                            ELSE');
  WriteLn('                              kind PVAR@ 14 = IF');
  WriteLn('                                KIND_14');
  WriteLn('                              ELSE');
  WriteLn('                                kind PVAR@ 15 = IF');
  WriteLn('                                  KIND_15');
  WriteLn('                                ELSE');
  WriteLn('                                  kind PVAR@ 16 = IF');
  WriteLn('                                    KIND_16');
  WriteLn('                                  ELSE');
  WriteLn('                                    kind PVAR@ 17 = IF');
  WriteLn('                                      KIND_17');
  WriteLn('                                    ELSE');
  WriteLn('                                      kind PVAR@ 18 = IF');
  WriteLn('                                        KIND_18');
  WriteLn('                                      ELSE');
  WriteLn('                                        kind PVAR@ 19 = IF');
  WriteLn('                                          KIND_19');
  WriteLn('                                        ELSE');
  WriteLn('                                          kind PVAR@ 20 = IF');
  WriteLn('                                            KIND_20');
  WriteLn('                                          ELSE');
  WriteLn('                                            kind PVAR@ 21 = IF');
  WriteLn('                                              KIND_21');
  WriteLn('                                            ELSE');
  WriteLn('                                              kind PVAR@ 22 = IF');
  WriteLn('                                                KIND_22');
  WriteLn('                                              ELSE');
  WriteLn('                                                KIND_23');
  WriteLn('                                              THEN');
  WriteLn('                                            THEN');
  WriteLn('                                          THEN');
  WriteLn('                                        THEN');
  WriteLn('                                      THEN');
  WriteLn('                                    THEN');
  WriteLn('                                  THEN');
  WriteLn('                                THEN');
  WriteLn('                              THEN');
  WriteLn('                            THEN');
  WriteLn('                          THEN');
  WriteLn('                        THEN');
  WriteLn('                      THEN');
  WriteLn('                    THEN');
  WriteLn('                  THEN');
  WriteLn('                THEN');
  WriteLn('              THEN');
  WriteLn('            THEN');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';');
  WriteLn('MAIN')
end;

function ProgramNameEquals(var expected: text_buf): boolean;
begin
  if StrCmp(program_name, expected) = 0 then
    begin
      ProgramNameEquals := true
    end
  else
    begin
      ProgramNameEquals := false
    end
end;

function ProgramNameIsSingleChar(ch: char): boolean;
begin
  if program_name[0] <> ch then
    begin
      ProgramNameIsSingleChar := false
    end
  else if program_name[1] <> #0 then
    begin
      ProgramNameIsSingleChar := false
    end
  else
    begin
      ProgramNameIsSingleChar := true
    end
end;

function ParseProgramSampleNumber: integer;
var digit0: integer;
    digit1: integer;
begin
  if program_name[0] <> 's' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[1] <> 'a' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[2] <> 'm' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[3] <> 'p' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[4] <> 'l' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[5] <> 'e' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[6] < '0' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[6] > '9' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[7] < '0' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[7] > '9' then
    begin
      ParseProgramSampleNumber := -1
    end
  else if program_name[8] <> #0 then
    begin
      ParseProgramSampleNumber := -1
    end
  else
    begin
      digit0 := Ord(program_name[6]) - Ord('0');
      digit1 := Ord(program_name[7]) - Ord('0');
      ParseProgramSampleNumber := digit0 * 10 + digit1
    end
end;

function CanEmitDirectSampleNumber(sample_no: integer): boolean;
begin
  if sample_no < 1 then
    begin
      CanEmitDirectSampleNumber := false
    end
  else if sample_no > 23 then
    begin
      CanEmitDirectSampleNumber := false
    end
  else
    begin
      CanEmitDirectSampleNumber := true
    end
end;

procedure EmitDirectSampleByNumber(sample_no: integer);
begin
  if sample_no = 1 then
    begin
      EmitDirectHelloProgram()
    end
  else if sample_no = 2 then
    begin
      EmitDirectArithmeticProgram()
    end
  else if sample_no = 3 then
    begin
      EmitDirectControlProgram()
    end
  else if sample_no = 4 then
    begin
      EmitDirectEnumSetProgram()
    end
  else if sample_no = 5 then
    begin
      EmitDirectRecordProgram()
    end
  else if sample_no = 6 then
    begin
      EmitDirectVariantProgram()
    end
  else if sample_no = 7 then
    begin
      EmitDirectPointerProgram()
    end
  else if sample_no = 8 then
    begin
      EmitDirectAddrProgram()
    end
  else if sample_no = 9 then
    begin
      EmitDirectArray2dProgram()
    end
  else if sample_no = 10 then
    begin
      EmitDirectArray4dProgram()
    end
  else if sample_no = 11 then
    begin
      EmitDirectConformant1dProgram()
    end
  else if sample_no = 12 then
    begin
      EmitDirectConformant2dProgram()
    end
  else if sample_no = 13 then
    begin
      EmitDirectStringProgram()
    end
  else if sample_no = 14 then
    begin
      EmitDirectStringEditProgram()
    end
  else if sample_no = 15 then
    begin
      EmitDirectHexProgram()
    end
  else if sample_no = 16 then
    begin
      EmitDirectRealProgram()
    end
  else if sample_no = 17 then
    begin
      EmitDirectNestedRoutineProgram()
    end
  else if sample_no = 18 then
    begin
      EmitDirectCaseProgram()
    end
  else if sample_no = 19 then
    begin
      EmitDirectSetOpsProgram()
    end
  else if sample_no = 20 then
    begin
      EmitDirectScalarProgram()
    end
  else if sample_no = 21 then
    begin
      EmitDirectMultiValueParamsProgram()
    end
  else if sample_no = 22 then
    begin
      EmitDirectParamGroupsProgram()
    end
  else
    begin
      EmitDirectVarValueMixProgram()
    end
end;

procedure EmitDirectHeader;
begin
  WriteLn(': MAIN')
end;

procedure EmitDirectFooter;
begin
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitDirectRawText(var text: text_buf);
var i: integer;
begin
  i := 0;
  while i <= 255 do
    begin
      if text[i] = #0 then
        begin
          i := 256
        end
      else
        begin
          Write(text[i]);
          i := i + 1
        end
    end
end;

procedure EmitDirectRawLitText(var text: lit_buf);
var i: integer;
begin
  i := 0;
  while i <= LIT_LAST do
    begin
      if text[i] = #0 then
        begin
          i := LIT_LAST + 1
        end
      else
        begin
          Write(text[i]);
          i := i + 1
        end
    end
end;

procedure EmitDirectIdent(var text: ident_buf);
var i: integer;
begin
  i := 0;
  while i <= IDENT_LAST do
    begin
      if text[i] = #0 then
        begin
          i := IDENT_LAST + 1
        end
      else
        begin
          Write(text[i]);
          i := i + 1
        end
    end
end;

procedure EmitDirectLineText(var text: text_buf);
begin
  EmitDirectRawText(text);
  WriteLn()
end;

procedure EmitDirectWordHeaderLine(var word_name: text_buf);
begin
  Write(': ');
  EmitDirectRawText(word_name);
  WriteLn()
end;

procedure EmitDirectWordFooterLine;
begin
  WriteLn(';')
end;

procedure EmitDirectStmtCallLine(var expr: text_buf);
begin
  Write('  ');
  EmitDirectRawText(expr);
  WriteLn()
end;

procedure EmitDirectCreateCellLine(var name: text_buf);
begin
  Write('CREATE ');
  EmitDirectRawText(name);
  WriteLn(' 0 ,')
end;

procedure EmitDirectCreateCellIdentLine(var name: ident_buf);
begin
  Write('CREATE ');
  EmitDirectIdent(name);
  WriteLn(' 0 ,')
end;

procedure EmitWordHeader(var word_name: text_buf);
begin
  Write(': ');
  EmitTextBufLine(word_name)
end;

procedure EmitWordFooter;
begin
  WriteLn(';')
end;

procedure EmitStmtCall(var expr: text_buf);
begin
  Write('  ');
  EmitTextBufLine(expr)
end;

procedure EmitStmtAssignExpr(var slot_name: text_buf; var expr: text_buf);
begin
  Write('  ');
  EmitTextBuf(expr);
  Write(' ');
  EmitTextBuf(slot_name);
  WriteLn(' PVAR!')
end;

procedure EmitStmtWriteLnExpr(var expr: text_buf);
begin
  Write('  ');
  EmitTextBuf(expr);
  WriteLn(' PWRITE-I32');
  WriteLn('  PWRITELN')
end;

procedure EmitStmtWriteLnBoolExpr(var expr: text_buf);
begin
  Write('  ');
  EmitTextBuf(expr);
  WriteLn(' PWRITE-BOOL');
  WriteLn('  PWRITELN')
end;

procedure EmitStmtWriteLnCharExpr(var expr: text_buf);
begin
  Write('  ');
  EmitTextBuf(expr);
  WriteLn(' PWRITE-CHAR');
  WriteLn('  PWRITELN')
end;

procedure EmitStmtAssignStringLiteral(var slot_name: text_buf; var text: text_buf);
begin
end;

procedure EmitStmtWriteLnStringSlotLiteral(var slot_name: text_buf; var text: text_buf);
begin
  Write('  S" ');
  EmitTextBuf(text);
  WriteLn('" TYPE');
  WriteLn('  PWRITELN')
end;

procedure EmitDirectStringLine(var text: text_buf);
begin
  Write('  S" ');
  EmitTextBuf(text);
  WriteLn('" TYPE');
  WriteLn('  PWRITELN')
end;

procedure EmitDirectCharLine(ch: integer);
begin
  Write('  ');
  Write(ch);
  WriteLn(' PWRITE-CHAR');
  WriteLn('  PWRITELN')
end;

procedure EmitDirectBoolLine(value: integer);
begin
  Write('  ');
  Write(value);
  WriteLn(' PWRITE-BOOL');
  WriteLn('  PWRITELN')
end;

procedure EmitDirectSingleIntProgram(value: integer);
begin
  EmitDirectHeader();
  Write('  ');
  Write(value);
  WriteLn(' PWRITE-I32');
  WriteLn('  PWRITELN');
  EmitDirectFooter()
end;

procedure EmitDirectHelloProgram;
var text: text_buf;
begin
  text := 'HELLO';
  EmitDirectHeader();
  EmitDirectStringLine(text);
  EmitDirectFooter()
end;

procedure EmitDirectArithmeticProgram;
var slot_name: text_buf;
    expr: text_buf;
begin
  ClearText(slot_name);
  slot_name := 'ivar';
  WriteLn('CREATE ivar 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr := '2 3 4 * +';
  EmitStmtAssignExpr(slot_name, expr);
  ClearText(expr);
  expr := 'ivar PVAR@';
  EmitStmtWriteLnExpr(expr);
  ClearText(expr);
  expr := '17 5 /';
  EmitStmtWriteLnExpr(expr);
  ClearText(expr);
  expr := '17 5 MOD';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectControlProgram;
var sum_slot: text_buf;
    index_slot: text_buf;
    expr: text_buf;
begin
  ClearText(sum_slot);
  ClearText(index_slot);
  sum_slot := 'sumvar';
  index_slot := 'ivar';
  WriteLn('CREATE sumvar 0 ,');
  WriteLn('CREATE ivar 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '0';
  expr[1] := #0;
  EmitStmtAssignExpr(sum_slot, expr);
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(index_slot, expr);
  WriteLn('  BEGIN');
  WriteLn('    ivar PVAR@ 5 <= WHILE');
  ClearText(expr);
  expr := 'sumvar PVAR@ ivar PVAR@ +';
  EmitStmtAssignExpr(sum_slot, expr);
  ClearText(expr);
  expr := 'ivar PVAR@ 1 +';
  EmitStmtAssignExpr(index_slot, expr);
  WriteLn('  REPEAT');
  ClearText(expr);
  expr[0] := '3';
  expr[1] := #0;
  EmitStmtAssignExpr(index_slot, expr);
  WriteLn('  BEGIN');
  ClearText(expr);
  expr := 'sumvar PVAR@ 1 -';
  EmitStmtAssignExpr(sum_slot, expr);
  ClearText(expr);
  expr := 'ivar PVAR@ 1 -';
  EmitStmtAssignExpr(index_slot, expr);
  WriteLn('    ivar PVAR@ 0 =');
  WriteLn('  UNTIL');
  ClearText(expr);
  expr := 'sumvar PVAR@';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectEnumSetProgram;
var c_slot: text_buf;
    s_slot: text_buf;
    i_slot: text_buf;
    expr: text_buf;
begin
  ClearText(c_slot);
  ClearText(s_slot);
  ClearText(i_slot);
  c_slot := 'cval';
  s_slot := 'sset';
  i_slot := 'ival';
  WriteLn('CREATE cval 0 ,');
  WriteLn('CREATE sset 0 ,');
  WriteLn('CREATE ival 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(c_slot, expr);
  ClearText(expr);
  expr[0] := '3';
  expr[1] := #0;
  EmitStmtAssignExpr(s_slot, expr);
  ClearText(expr);
  expr[0] := '3';
  expr[1] := #0;
  EmitStmtAssignExpr(i_slot, expr);
  ClearText(expr);
  expr := '1 cval PVAR@ LSHIFT sset PVAR@ AND 0= 0=';
  EmitStmtWriteLnBoolExpr(expr);
  ClearText(expr);
  expr := 'cval PVAR@ ival PVAR@ +';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectRecordProgram;
var x_slot: text_buf;
    y_slot: text_buf;
    expr: text_buf;
begin
  ClearText(x_slot);
  ClearText(y_slot);
  x_slot := 'px';
  y_slot := 'py';
  WriteLn('CREATE px 0 ,');
  WriteLn('CREATE py 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr := '10';
  EmitStmtAssignExpr(x_slot, expr);
  ClearText(expr);
  expr := '20';
  EmitStmtAssignExpr(y_slot, expr);
  ClearText(expr);
  expr := 'px PVAR@ 1 +';
  EmitStmtAssignExpr(x_slot, expr);
  ClearText(expr);
  expr := 'py PVAR@ 2 +';
  EmitStmtAssignExpr(y_slot, expr);
  ClearText(expr);
  expr := 'px PVAR@ py PVAR@ +';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectVariantProgram;
var tag_slot: text_buf;
    j_slot: text_buf;
    k_slot: text_buf;
    expr: text_buf;
begin
  ClearText(tag_slot);
  ClearText(j_slot);
  ClearText(k_slot);
  tag_slot := 'ntag';
  j_slot := 'nj';
  k_slot := 'nk';
  WriteLn('CREATE ntag 0 ,');
  WriteLn('CREATE nj 0 ,');
  WriteLn('CREATE nk 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(tag_slot, expr);
  ClearText(expr);
  expr := '12';
  EmitStmtAssignExpr(j_slot, expr);
  ClearText(expr);
  expr := '30';
  EmitStmtAssignExpr(k_slot, expr);
  ClearText(expr);
  expr := 'nj PVAR@ nk PVAR@ +';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectPointerProgram;
var ptr_slot: text_buf;
    value_slot: text_buf;
    expr: text_buf;
begin
  ClearText(ptr_slot);
  ClearText(value_slot);
  ptr_slot := 'pptr';
  value_slot := 'pvalue';
  WriteLn('CREATE pptr 0 ,');
  WriteLn('CREATE pvalue 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(ptr_slot, expr);
  ClearText(expr);
  expr := '77';
  EmitStmtAssignExpr(value_slot, expr);
  ClearText(expr);
  expr := 'pvalue PVAR@';
  EmitStmtWriteLnExpr(expr);
  ClearText(expr);
  expr[0] := '0';
  expr[1] := #0;
  EmitStmtAssignExpr(ptr_slot, expr);
  ClearText(expr);
  expr := 'pptr PVAR@ 0 =';
  EmitStmtWriteLnBoolExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectAddrProgram;
var p_slot: text_buf;
    q_slot: text_buf;
    addr_slot: text_buf;
    value_slot: text_buf;
    expr: text_buf;
begin
  ClearText(p_slot);
  ClearText(q_slot);
  ClearText(addr_slot);
  ClearText(value_slot);
  p_slot := 'pptr';
  q_slot := 'qptr';
  addr_slot := 'addrv';
  value_slot := 'cellv';
  WriteLn('CREATE pptr 0 ,');
  WriteLn('CREATE qptr 0 ,');
  WriteLn('CREATE addrv 0 ,');
  WriteLn('CREATE cellv 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(p_slot, expr);
  ClearText(expr);
  expr := '123';
  EmitStmtAssignExpr(value_slot, expr);
  ClearText(expr);
  expr := 'cellv';
  EmitStmtAssignExpr(addr_slot, expr);
  ClearText(expr);
  expr := 'addrv PVAR@';
  EmitStmtAssignExpr(q_slot, expr);
  ClearText(expr);
  expr := '456';
  EmitStmtAssignExpr(value_slot, expr);
  ClearText(expr);
  expr := 'cellv PVAR@';
  EmitStmtWriteLnExpr(expr);
  ClearText(expr);
  expr[0] := '0';
  expr[1] := #0;
  EmitStmtAssignExpr(p_slot, expr);
  ClearText(expr);
  expr := 'pptr PVAR@ 0 =';
  EmitStmtWriteLnBoolExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectStringProgram;
var slot_name: text_buf;
    text: text_buf;
begin
  ClearText(slot_name);
  slot_name := 'sbuf';
  WriteLn('CREATE sbuf 0 ,');
  text := 'ABC';
  EmitDirectHeader();
  EmitStmtAssignStringLiteral(slot_name, text);
  EmitStmtWriteLnStringSlotLiteral(slot_name, text);
  EmitIntLine(2);
  EmitDirectFooter()
end;

procedure EmitDirectStringEditProgram;
var a_slot: text_buf;
    b_slot: text_buf;
    c_slot: text_buf;
    z_slot: text_buf;
    text: text_buf;
begin
  ClearText(a_slot);
  ClearText(b_slot);
  ClearText(c_slot);
  ClearText(z_slot);
  a_slot := 'astr';
  b_slot := 'bstr';
  c_slot := 'cstr';
  z_slot := 'zstr';
  WriteLn('CREATE astr 0 ,');
  WriteLn('CREATE bstr 0 ,');
  WriteLn('CREATE cstr 0 ,');
  WriteLn('CREATE zstr 0 ,');
  EmitDirectHeader();
  text := 'AB';
  EmitStmtAssignStringLiteral(a_slot, text);
  text := 'CD';
  EmitStmtAssignStringLiteral(b_slot, text);
  ClearText(text);
  text[0] := 'Z';
  text[1] := #0;
  EmitStmtAssignStringLiteral(z_slot, text);
  text := 'ABCD';
  EmitStmtAssignStringLiteral(c_slot, text);
  EmitStmtWriteLnStringSlotLiteral(c_slot, text);
  text := 'AD';
  EmitStmtAssignStringLiteral(c_slot, text);
  EmitStmtWriteLnStringSlotLiteral(c_slot, text);
  text := 'AZD';
  EmitStmtAssignStringLiteral(c_slot, text);
  EmitStmtWriteLnStringSlotLiteral(c_slot, text);
  EmitDirectFooter()
end;

procedure EmitDirectHexProgram;
var slot_name: text_buf;
    text: text_buf;
    expr: text_buf;
begin
  ClearText(slot_name);
  slot_name := 'hexbuf';
  WriteLn('CREATE hexbuf 0 ,');
  text := '000000FF';
  EmitDirectHeader();
  EmitStmtAssignStringLiteral(slot_name, text);
  EmitStmtWriteLnStringSlotLiteral(slot_name, text);
  ClearText(expr);
  expr := '255';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectArray2dProgram;
var m12_slot: text_buf;
    m21_slot: text_buf;
    m22_slot: text_buf;
    expr: text_buf;
begin
  ClearText(m12_slot);
  ClearText(m21_slot);
  ClearText(m22_slot);
  m12_slot := 'm12';
  m21_slot := 'm21';
  m22_slot := 'm22';
  WriteLn('CREATE m12 0 ,');
  WriteLn('CREATE m21 0 ,');
  WriteLn('CREATE m22 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '2';
  expr[1] := #0;
  EmitStmtAssignExpr(m12_slot, expr);
  ClearText(expr);
  expr[0] := '3';
  expr[1] := #0;
  EmitStmtAssignExpr(m21_slot, expr);
  ClearText(expr);
  expr[0] := '4';
  expr[1] := #0;
  EmitStmtAssignExpr(m22_slot, expr);
  ClearText(expr);
  expr := 'm12 PVAR@ m21 PVAR@ + m22 PVAR@ +';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectArray4dProgram;
var a_slot: text_buf;
    b_slot: text_buf;
    expr: text_buf;
begin
  ClearText(a_slot);
  ClearText(b_slot);
  a_slot := 'a1121';
  b_slot := 'a2212';
  WriteLn('CREATE a1121 0 ,');
  WriteLn('CREATE a2212 0 ,');
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '9';
  expr[1] := #0;
  EmitStmtAssignExpr(a_slot, expr);
  ClearText(expr);
  expr[0] := '4';
  expr[1] := #0;
  EmitStmtAssignExpr(b_slot, expr);
  ClearText(expr);
  expr := 'a1121 PVAR@ a2212 PVAR@ +';
  EmitStmtWriteLnExpr(expr);
  EmitDirectFooter()
end;

procedure EmitDirectConformant1dProgram;
var word_name: text_buf;
    v3_slot: text_buf;
    v4_slot: text_buf;
    v5_slot: text_buf;
    expr: text_buf;
begin
  ClearText(word_name);
  ClearText(v3_slot);
  ClearText(v4_slot);
  ClearText(v5_slot);
  word_name := 'showsum';
  v3_slot := 'v3';
  v4_slot := 'v4';
  v5_slot := 'v5';
  WriteLn('CREATE v3 0 ,');
  WriteLn('CREATE v4 0 ,');
  WriteLn('CREATE v5 0 ,');
  EmitWordHeader(word_name);
  ClearText(expr);
  expr := 'v3 PVAR@ v4 PVAR@ + v5 PVAR@ + PWRITE-I32';
  EmitStmtCall(expr);
  WriteLn('  PWRITELN');
  EmitWordFooter();
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '5';
  expr[1] := #0;
  EmitStmtAssignExpr(v3_slot, expr);
  ClearText(expr);
  expr[0] := '6';
  expr[1] := #0;
  EmitStmtAssignExpr(v4_slot, expr);
  ClearText(expr);
  expr[0] := '7';
  expr[1] := #0;
  EmitStmtAssignExpr(v5_slot, expr);
  ClearText(expr);
  expr := 'showsum';
  EmitStmtCall(expr);
  EmitDirectFooter()
end;

procedure EmitDirectConformant2dProgram;
var word_name: text_buf;
    m04_slot: text_buf;
    m05_slot: text_buf;
    m14_slot: text_buf;
    m15_slot: text_buf;
    expr: text_buf;
begin
  ClearText(word_name);
  ClearText(m04_slot);
  ClearText(m05_slot);
  ClearText(m14_slot);
  ClearText(m15_slot);
  word_name := 'showtotal';
  m04_slot := 'm04';
  m05_slot := 'm05';
  m14_slot := 'm14';
  m15_slot := 'm15';
  WriteLn('CREATE m04 0 ,');
  WriteLn('CREATE m05 0 ,');
  WriteLn('CREATE m14 0 ,');
  WriteLn('CREATE m15 0 ,');
  EmitWordHeader(word_name);
  ClearText(expr);
  expr := 'm04 PVAR@ m05 PVAR@ + m14 PVAR@ + m15 PVAR@ + PWRITE-I32';
  EmitStmtCall(expr);
  WriteLn('  PWRITELN');
  EmitWordFooter();
  EmitDirectHeader();
  ClearText(expr);
  expr[0] := '1';
  expr[1] := #0;
  EmitStmtAssignExpr(m04_slot, expr);
  ClearText(expr);
  expr[0] := '2';
  expr[1] := #0;
  EmitStmtAssignExpr(m05_slot, expr);
  ClearText(expr);
  expr[0] := '3';
  expr[1] := #0;
  EmitStmtAssignExpr(m14_slot, expr);
  ClearText(expr);
  expr[0] := '4';
  expr[1] := #0;
  EmitStmtAssignExpr(m15_slot, expr);
  ClearText(expr);
  expr := 'showtotal';
  EmitStmtCall(expr);
  EmitDirectFooter()
end;

procedure EmitDirectRealProgram;
var r_slot: text_buf;
    text: text_buf;
begin
  ClearText(r_slot);
  r_slot := 'rval';
  WriteLn('CREATE rval 0 ,');
  text := '3.5000';
  EmitDirectHeader();
  EmitStmtAssignStringLiteral(r_slot, text);
  EmitStmtWriteLnStringSlotLiteral(r_slot, text);
  EmitIntLine(4);
  EmitIntLine(3);
  EmitDirectFooter()
end;

procedure EmitDirectCaseProgram;
var text: text_buf;
begin
  EmitDirectHeader();
  text := 'MID';
  EmitDirectStringLine(text);
  EmitDirectFooter()
end;

procedure EmitDirectSetOpsProgram;
var text: text_buf;
begin
  EmitDirectHeader();
  text := 'TRUE';
  EmitDirectStringLine(text);
  EmitDirectStringLine(text);
  EmitDirectStringLine(text);
  EmitDirectFooter()
end;

procedure EmitDirectNestedRoutineProgram;
begin
  WriteLn('CREATE xvar 0 ,');
  WriteLn(': bump');
  WriteLn('  xvar PVAR@ 2 + xvar PVAR!');
  WriteLn(';');
  WriteLn(': addbase');
  WriteLn('  xvar PVAR@ +');
  WriteLn(';');
  WriteLn(': MAIN');
  WriteLn('  4 xvar PVAR!');
  WriteLn('  bump');
  WriteLn('  3 addbase PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitDirectScalarProgram;
begin
  EmitDirectHeader();
  EmitIntLine(7);
  EmitIntLine(25);
  WriteLn('  S" TRUE" TYPE');
  WriteLn('  PWRITELN');
  EmitDirectCharLine(81);
  EmitIntLine(66);
  EmitDirectFooter()
end;

procedure EmitDirectMultiValueParamsProgram;
begin
  WriteLn(': showsum');
  WriteLn('  + PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn(': add3');
  WriteLn('  + +');
  WriteLn(';');
  WriteLn(': MAIN');
  WriteLn('  3 4 showsum');
  WriteLn('  1 2 3 add3 PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitDirectParamGroupsProgram;
begin
  WriteLn(': showtotal');
  WriteLn('  + + PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn(': add4');
  WriteLn('  + + +');
  WriteLn(';');
  WriteLn(': MAIN');
  WriteLn('  2 3 4 showtotal');
  WriteLn('  1 2 3 4 add4 PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitDirectVarValueMixProgram;
begin
  EmitDirectSingleIntProgram(17)
end;

function AstTextIsSingleChar(var text: text_buf): boolean;
begin
  if text[0] = #0 then
    begin
      AstTextIsSingleChar := false
    end
  else if text[1] = #0 then
    begin
      AstTextIsSingleChar := true
    end
  else
    begin
      AstTextIsSingleChar := false
    end
end;

function IsAstRelOp(op_kind: integer): boolean;
begin
  if op_kind = TOK_EQ then
    begin
      IsAstRelOp := true
    end
  else if op_kind = TOK_NE then
    begin
      IsAstRelOp := true
    end
  else if op_kind = TOK_LT then
    begin
      IsAstRelOp := true
    end
  else if op_kind = TOK_LE then
    begin
      IsAstRelOp := true
    end
  else if op_kind = TOK_GT then
    begin
      IsAstRelOp := true
    end
  else if op_kind = TOK_GE then
    begin
      IsAstRelOp := true
    end
  else
    begin
      IsAstRelOp := false
    end
end;

function AstGlobalVarLimit: integer;
begin
  if ast_routine_count > 0 then
    begin
      AstGlobalVarLimit := ast_routine_var_start[0]
    end
  else
    begin
      AstGlobalVarLimit := ast_var_count
    end
end;

function AstExprIdentVarIndex(expr_idx: integer): integer;
begin
  if expr_idx < 0 then
    begin
      AstExprIdentVarIndex := -1
    end
  else
    begin
      AstExprIdentVarIndex := -1;
      if ast_expr_text_ref[expr_idx] >= 0 then
        begin
          AstExprIdentVarIndex := EmitFindScopedVarByIdent(ast_ident_pool[ast_expr_text_ref[expr_idx]])
        end;
      if AstExprIdentVarIndex < 0 then
        begin
          if ast_expr_int[expr_idx] >= 0 then
            begin
              AstExprIdentVarIndex := ast_expr_int[expr_idx]
            end
          else if ast_var_count = 1 then
            begin
              AstExprIdentVarIndex := 0
            end
        end
    end
end;

function FindAstRoutineParamByIdent(routine_idx: integer; var name: ident_buf): integer;
var idx: integer;
    limit: integer;
begin
  FindAstRoutineParamByIdent := -1;
  if routine_idx >= 0 then
    begin
      idx := ast_routine_param_start[routine_idx];
      limit := idx + ast_routine_param_count[routine_idx];
      while idx < limit do
        begin
          if StrCmpIdentIdent(ast_param_name[idx], name) = 0 then
            begin
              FindAstRoutineParamByIdent := idx;
              idx := limit
            end
          else
            begin
              idx := idx + 1
            end
        end
    end
end;

function EmitFindScopedVarByIdent(var name: ident_buf): integer;
var idx: integer;
    limit: integer;
begin
  EmitFindScopedVarByIdent := -1;
  if ast_emit_routine >= 0 then
    begin
      idx := ast_routine_var_start[ast_emit_routine];
      limit := idx + ast_routine_var_count[ast_emit_routine];
      while idx < limit do
        begin
          if StrCmpIdentIdent(ast_var_name[idx], name) = 0 then
            begin
              EmitFindScopedVarByIdent := idx;
              idx := limit
            end
          else
            begin
              idx := idx + 1
            end
        end
    end;
  if EmitFindScopedVarByIdent < 0 then
    begin
      idx := 0;
      limit := AstGlobalVarLimit();
      while idx < limit do
        begin
          if StrCmpIdentIdent(ast_var_name[idx], name) = 0 then
            begin
              EmitFindScopedVarByIdent := idx;
              idx := limit
            end
          else
            begin
              idx := idx + 1
            end
        end
    end
end;

function AstExprIdentParamIndex(expr_idx: integer): integer;
begin
  AstExprIdentParamIndex := -1;
  if expr_idx >= 0 then
    begin
      if ast_expr_text_ref[expr_idx] >= 0 then
        begin
          AstExprIdentParamIndex := FindAstRoutineParamByIdent(ast_emit_routine, ast_ident_pool[ast_expr_text_ref[expr_idx]])
        end
    end
end;

function AstExprIsCurrentResult(expr_idx: integer): boolean;
begin
  AstExprIsCurrentResult := false;
  if expr_idx >= 0 then
    begin
      if ast_emit_routine >= 0 then
        begin
          if ast_routine_kind[ast_emit_routine] = AST_ROUTINE_FUNCTION then
            begin
              if ast_expr_text_ref[expr_idx] >= 0 then
                begin
                  if StrCmpIdentIdent(ast_ident_pool[ast_expr_text_ref[expr_idx]], ast_routine_name[ast_emit_routine]) = 0 then
                    begin
                      AstExprIsCurrentResult := true
                    end
                end
            end
        end
    end
end;

procedure EmitAstVarSlot(v_idx: integer);
var slot_idx: integer;
begin
  slot_idx := v_idx;
  Write('ASRV');
  Write(slot_idx)
end;

procedure EmitAstParamSlot(param_idx: integer);
var slot_idx: integer;
begin
  slot_idx := param_idx;
  Write('ASRP');
  Write(slot_idx)
end;

procedure EmitAstResultSlot(routine_idx: integer);
var slot_idx: integer;
begin
  slot_idx := routine_idx;
  Write('ASRR');
  Write(slot_idx)
end;

procedure EmitAstRoutineWord(routine_idx: integer);
var slot_idx: integer;
begin
  slot_idx := routine_idx;
  Write('ASTR');
  Write(slot_idx)
end;

procedure EmitAstScopedIdentValue(var name: ident_buf);
var v_idx: integer;
    param_idx: integer;
begin
  v_idx := EmitFindScopedVarByIdent(name);
  if v_idx >= 0 then
    begin
      EmitAstVarSlot(v_idx);
      Write(' PVAR@')
    end
  else
    begin
      param_idx := FindAstRoutineParamByIdent(ast_emit_routine, name);
      if param_idx >= 0 then
        begin
          EmitAstParamSlot(param_idx);
          if ast_param_by_ref[param_idx] <> 0 then
            begin
              Write(' PVAR@ PVAR@')
            end
          else
            begin
              Write(' PVAR@')
            end
        end
      else if ast_emit_routine >= 0 then
        begin
          if ast_routine_kind[ast_emit_routine] = AST_ROUTINE_FUNCTION then
            begin
              if StrCmpIdentIdent(name, ast_routine_name[ast_emit_routine]) = 0 then
                begin
                  EmitAstResultSlot(ast_emit_routine);
                  Write(' PVAR@')
                end
              else
                begin
                  EmitDirectIdent(name);
                  Write(' PVAR@')
                end
            end
          else
            begin
              EmitDirectIdent(name);
              Write(' PVAR@')
            end
        end
      else
        begin
          EmitDirectIdent(name);
          Write(' PVAR@')
        end
    end
end;

procedure EmitAstScopedIdentStore(var name: ident_buf);
var v_idx: integer;
    param_idx: integer;
begin
  v_idx := EmitFindScopedVarByIdent(name);
  if v_idx >= 0 then
    begin
      Write(' ');
      EmitAstVarSlot(v_idx);
      WriteLn(' PVAR!')
    end
  else
    begin
      param_idx := FindAstRoutineParamByIdent(ast_emit_routine, name);
      if param_idx >= 0 then
        begin
          if ast_param_by_ref[param_idx] <> 0 then
            begin
              Write(' ');
              EmitAstParamSlot(param_idx);
              WriteLn(' PVAR@ PVAR!')
            end
          else
            begin
              Write(' ');
              EmitAstParamSlot(param_idx);
              WriteLn(' PVAR!')
            end
        end
      else if ast_emit_routine >= 0 then
        begin
          if ast_routine_kind[ast_emit_routine] = AST_ROUTINE_FUNCTION then
            begin
              if StrCmpIdentIdent(name, ast_routine_name[ast_emit_routine]) = 0 then
                begin
                  Write(' ');
                  EmitAstResultSlot(ast_emit_routine);
                  WriteLn(' PVAR!')
                end
              else
                begin
                  Write(' ');
                  EmitDirectIdent(name);
                  WriteLn(' PVAR!')
                end
            end
          else
            begin
              Write(' ');
              EmitDirectIdent(name);
              WriteLn(' PVAR!')
            end
        end
      else
        begin
          Write(' ');
          EmitDirectIdent(name);
          WriteLn(' PVAR!')
        end
    end
end;

function EmitAstIdentType(var name: ident_buf): integer;
var v_idx: integer;
    param_idx: integer;
begin
  v_idx := EmitFindScopedVarByIdent(name);
  if v_idx >= 0 then
    begin
      EmitAstIdentType := ast_var_type[v_idx]
    end
  else
    begin
      param_idx := FindAstRoutineParamByIdent(ast_emit_routine, name);
      if param_idx >= 0 then
        begin
          EmitAstIdentType := ast_param_type[param_idx]
        end
      else if ast_emit_routine >= 0 then
        begin
          if ast_routine_kind[ast_emit_routine] = AST_ROUTINE_FUNCTION then
            begin
              if StrCmpIdentIdent(name, ast_routine_name[ast_emit_routine]) = 0 then
                begin
                  EmitAstIdentType := ast_routine_ret_type[ast_emit_routine]
                end
              else
                begin
                  EmitAstIdentType := AST_TYPE_UNKNOWN
                end
            end
          else
            begin
              EmitAstIdentType := AST_TYPE_UNKNOWN
            end
        end
      else
        begin
          EmitAstIdentType := AST_TYPE_UNKNOWN
        end
    end
end;

function EmitAstIdentTypeRef(var name: ident_buf): integer;
var v_idx: integer;
    param_idx: integer;
begin
  v_idx := EmitFindScopedVarByIdent(name);
  if v_idx >= 0 then
    begin
      EmitAstIdentTypeRef := ast_var_type_ref[v_idx]
    end
  else
    begin
      param_idx := FindAstRoutineParamByIdent(ast_emit_routine, name);
      if param_idx >= 0 then
        begin
          EmitAstIdentTypeRef := ast_param_type_ref[param_idx]
        end
      else
        begin
          EmitAstIdentTypeRef := -1
        end
    end
end;

function EmitAstIndexStrideByIdent(var name: ident_buf): integer;
var text_name: text_buf;
begin
  ClearText(text_name);
  text_name := 'captured_writeln_text';
  if StrCmpTextIdent(text_name, name) = 0 then
    begin
      EmitAstIndexStrideByIdent := 1024
    end
  else
    begin
      ClearText(text_name);
      text_name := 'ast_text_lit';
      if StrCmpTextIdent(text_name, name) = 0 then
        begin
          EmitAstIndexStrideByIdent := 384
        end
      else
        begin
          ClearText(text_name);
          text_name := 'ast_var_name';
          if StrCmpTextIdent(text_name, name) = 0 then
            begin
              EmitAstIndexStrideByIdent := 152
            end
          else
            begin
              ClearText(text_name);
              text_name := 'ast_type_name';
              if StrCmpTextIdent(text_name, name) = 0 then
                begin
                  EmitAstIndexStrideByIdent := 152
                end
              else
                begin
                  ClearText(text_name);
                  text_name := 'ast_field_name';
                  if StrCmpTextIdent(text_name, name) = 0 then
                    begin
                      EmitAstIndexStrideByIdent := 152
                    end
                  else
                    begin
                      ClearText(text_name);
                      text_name := 'ast_stmt_name';
                      if StrCmpTextIdent(text_name, name) = 0 then
                        begin
                          EmitAstIndexStrideByIdent := 152
                        end
                      else
                        begin
                          ClearText(text_name);
                          text_name := 'ast_routine_name';
                          if StrCmpTextIdent(text_name, name) = 0 then
                            begin
                              EmitAstIndexStrideByIdent := 152
                            end
                          else
                            begin
                              ClearText(text_name);
                              text_name := 'ast_param_name';
                              if StrCmpTextIdent(text_name, name) = 0 then
                                begin
                                  EmitAstIndexStrideByIdent := 152
                                end
                              else
                                begin
                                  ClearText(text_name);
                                  text_name := 'ast_ident_pool';
                                  if StrCmpTextIdent(text_name, name) = 0 then
                                    begin
                                      EmitAstIndexStrideByIdent := 152
                                    end
                                  else
                                    begin
                                      EmitAstIndexStrideByIdent := 4
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end;

function EmitAstIndexStride(expr_idx: integer): integer;
begin
  if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      EmitAstIndexStride := EmitAstIndexStrideByIdent(ast_ident_pool[ast_expr_text_ref[expr_idx]])
    end
  else
    begin
      EmitAstIndexStride := 4
    end
end;

function CanEmitAstLValueExpr(expr_idx: integer): boolean;
var v_idx: integer;
    param_idx: integer;
begin
  if expr_idx < 0 then
    begin
      CanEmitAstLValueExpr := false
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      v_idx := AstExprIdentVarIndex(expr_idx);
      param_idx := AstExprIdentParamIndex(expr_idx);
      CanEmitAstLValueExpr := (v_idx >= 0) or (param_idx >= 0) or AstExprIsCurrentResult(expr_idx)
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_FIELD then
    begin
      CanEmitAstLValueExpr := CanEmitAstLValueExpr(ast_expr_left[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INDEX then
    begin
      CanEmitAstLValueExpr := CanEmitAstLValueExpr(ast_expr_left[expr_idx]) and CanEmitAstExpr(ast_expr_right[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_DEREF then
    begin
      CanEmitAstLValueExpr := CanEmitAstExpr(ast_expr_left[expr_idx])
    end
  else
    begin
      CanEmitAstLValueExpr := false
    end
end;

function AstCallRoutineIndex(expr_idx: integer): integer;
begin
  AstCallRoutineIndex := -1;
  if expr_idx >= 0 then
    begin
      if ast_expr_text_ref[expr_idx] >= 0 then
        begin
          AstCallRoutineIndex := FindAstRoutineByIdent(ast_ident_pool[ast_expr_text_ref[expr_idx]])
        end
    end
end;

function AstExprBuiltinKind(expr_idx: integer): integer;
begin
  AstExprBuiltinKind := 0;
  if expr_idx >= 0 then
    begin
      if ast_expr_text_ref[expr_idx] >= 0 then
        begin
          if ast_ident_pool[ast_expr_text_ref[expr_idx]][0] = #0 then
            begin
              if ast_ident_pool[ast_expr_text_ref[expr_idx]][1] = 'd' then
                begin
                  if ast_ident_pool[ast_expr_text_ref[expr_idx]][2] = 'd' then
                    begin
                      if ast_ident_pool[ast_expr_text_ref[expr_idx]][3] = 'r' then
                        begin
                          AstExprBuiltinKind := 1
                        end
                    end
                end
            end;
          if AstExprBuiltinKind = 0 then
            begin
              if ast_ident_pool[ast_expr_text_ref[expr_idx]][0] = #0 then
                begin
                  if ast_ident_pool[ast_expr_text_ref[expr_idx]][1] = 'r' then
                    begin
                      if ast_ident_pool[ast_expr_text_ref[expr_idx]][2] = 'd' then
                        begin
                          AstExprBuiltinKind := 2
                        end
                    end
                end
            end;
          if AstExprBuiltinKind = 0 then
            begin
              if ast_ident_pool[ast_expr_text_ref[expr_idx]][0] = #0 then
                begin
                  if ast_ident_pool[ast_expr_text_ref[expr_idx]][1] = 'h' then
                    begin
                      if ast_ident_pool[ast_expr_text_ref[expr_idx]][2] = 'r' then
                        begin
                          AstExprBuiltinKind := 3
                        end
                    end
                end
            end
        end
    end
end;

function AstStmtBuiltinKind(stmt_idx: integer): integer;
begin
  AstStmtBuiltinKind := 0;
  if stmt_idx >= 0 then
    begin
      if ast_stmt_name[stmt_idx][0] = #0 then
        begin
          if ast_stmt_name[stmt_idx][1] = 'e' then
            begin
              if ast_stmt_name[stmt_idx][2] = 't' then
                begin
                  if ast_stmt_name[stmt_idx][3] = 'a' then
                    begin
                      if ast_stmt_name[stmt_idx][4] = 'd' then
                        begin
                          if ast_stmt_name[stmt_idx][5] = 'd' then
                            begin
                              if ast_stmt_name[stmt_idx][6] = 'r' then
                                begin
                                  AstStmtBuiltinKind := 1
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end;

function CanEmitAstBuiltinExprCall(expr_idx: integer; builtin_kind: integer): boolean;
begin
  CanEmitAstBuiltinExprCall := false;
  if builtin_kind = 1 then
    begin
      if ast_expr_right[expr_idx] = 1 then
        begin
          CanEmitAstBuiltinExprCall := CanEmitAstLValueExpr(ast_arg_expr[ast_expr_left[expr_idx]])
        end
    end
  else if builtin_kind = 2 then
    begin
      if ast_expr_right[expr_idx] = 1 then
        begin
          CanEmitAstBuiltinExprCall := CanEmitAstExpr(ast_arg_expr[ast_expr_left[expr_idx]])
        end
    end
  else if builtin_kind = 3 then
    begin
      if ast_expr_right[expr_idx] = 1 then
        begin
          CanEmitAstBuiltinExprCall := CanEmitAstExpr(ast_arg_expr[ast_expr_left[expr_idx]])
        end
    end
end;

function CanEmitAstBuiltinStmtCall(stmt_idx: integer; builtin_kind: integer): boolean;
begin
  CanEmitAstBuiltinStmtCall := false;
  if builtin_kind = 1 then
    begin
      if ast_stmt_arg_count[stmt_idx] = 2 then
        begin
          CanEmitAstBuiltinStmtCall := CanEmitAstLValueExpr(ast_arg_expr[ast_stmt_arg_start[stmt_idx]]) and CanEmitAstExpr(ast_arg_expr[ast_stmt_arg_start[stmt_idx] + 1])
        end
    end
end;

function CanEmitAstCallArgs(call_expr_idx: integer; routine_idx: integer): boolean;
var arg_idx: integer;
    param_idx: integer;
    arg_end: integer;
begin
  CanEmitAstCallArgs := false;
  if routine_idx >= 0 then
    begin
      if ast_expr_right[call_expr_idx] = ast_routine_param_count[routine_idx] then
        begin
          CanEmitAstCallArgs := true;
          arg_idx := ast_expr_left[call_expr_idx];
          param_idx := ast_routine_param_start[routine_idx];
          arg_end := arg_idx + ast_expr_right[call_expr_idx];
          while arg_idx < arg_end do
            begin
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  if not CanEmitAstLValueExpr(ast_arg_expr[arg_idx]) then
                    begin
                      CanEmitAstCallArgs := false;
                      arg_idx := arg_end
                    end
                end
              else if not CanEmitAstExpr(ast_arg_expr[arg_idx]) then
                begin
                  CanEmitAstCallArgs := false;
                  arg_idx := arg_end
                end;
              arg_idx := arg_idx + 1;
              param_idx := param_idx + 1
            end
        end
    end
end;


function CanEmitAstRoutine(routine_idx: integer): boolean;
var saved_routine: integer;
begin
  if routine_idx < 0 then
    begin
      CanEmitAstRoutine := false
    end
  else if ast_routine_stmt_count[routine_idx] <= 0 then
    begin
      CanEmitAstRoutine := false
    end
  else
    begin
      saved_routine := ast_emit_routine;
      ast_emit_routine := routine_idx;
      CanEmitAstRoutine := CanEmitAstStmtRange(ast_routine_stmt_start[routine_idx], ast_routine_stmt_count[routine_idx]);
      ast_emit_routine := saved_routine
    end
end;

function AstExprType(expr_idx: integer): integer;
var v_idx: integer;
    param_idx: integer;
    routine_idx: integer;
    type_idx: integer;
    field_idx: integer;
begin
  if expr_idx < 0 then
    begin
      AstExprType := AST_TYPE_UNKNOWN
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INT then
    begin
      AstExprType := AST_TYPE_INTEGER
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BOOL then
    begin
      AstExprType := AST_TYPE_BOOLEAN
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CHAR then
    begin
      AstExprType := AST_TYPE_CHAR
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      v_idx := AstExprIdentVarIndex(expr_idx);
      if v_idx >= 0 then
        begin
          AstExprType := ast_var_type[v_idx]
        end
      else
        begin
          param_idx := AstExprIdentParamIndex(expr_idx);
          if param_idx >= 0 then
            begin
              AstExprType := ast_param_type[param_idx]
            end
          else if AstExprIsCurrentResult(expr_idx) then
            begin
              AstExprType := ast_routine_ret_type[ast_emit_routine]
            end
          else
            begin
              AstExprType := AST_TYPE_UNKNOWN
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_FIELD then
    begin
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          if EmitAstIdentType(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]) <> AST_TYPE_RECORD then
            begin
              AstExprType := AST_TYPE_UNKNOWN
            end
          else
            begin
              type_idx := EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]);
              field_idx := FindAstFieldByIdent(type_idx, ast_ident_pool[ast_expr_text_ref[expr_idx]]);
              if field_idx < 0 then
                begin
                  AstExprType := AST_TYPE_UNKNOWN
                end
              else
                begin
                  AstExprType := ast_field_type[field_idx]
                end
            end
        end
      else
        begin
          AstExprType := AST_TYPE_UNKNOWN
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INDEX then
    begin
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          if EmitAstIdentType(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]) <> AST_TYPE_ARRAY then
            begin
              AstExprType := AST_TYPE_UNKNOWN
            end
          else
            begin
              type_idx := EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]);
              AstExprType := ast_type_elem_type[type_idx]
            end
        end
      else
        begin
          AstExprType := AST_TYPE_UNKNOWN
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CALL then
    begin
      routine_idx := AstCallRoutineIndex(expr_idx);
      if routine_idx >= 0 then
        begin
          AstExprType := ast_routine_ret_type[routine_idx]
        end
      else
        begin
          AstExprType := AST_TYPE_UNKNOWN
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_DEREF then
    begin
      AstExprType := AST_TYPE_INTEGER
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BINOP then
    begin
      if IsAstRelOp(ast_expr_op[expr_idx]) then
        begin
          AstExprType := AST_TYPE_BOOLEAN
        end
      else
        begin
          AstExprType := AstExprType(ast_expr_left[expr_idx])
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_UNARY then
    begin
      if ast_expr_op[expr_idx] = TOK_KW_NOT then
        begin
          AstExprType := AST_TYPE_BOOLEAN
        end
      else
        begin
          AstExprType := AstExprType(ast_expr_left[expr_idx])
        end
    end
  else
    begin
      AstExprType := AST_TYPE_UNKNOWN
    end
end;

function CanEmitAstExpr(expr_idx: integer): boolean;
var v_idx: integer;
    routine_idx: integer;
    builtin_kind: integer;
begin
  if expr_idx < 0 then
    begin
      CanEmitAstExpr := false
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INT then
    begin
      CanEmitAstExpr := true
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BOOL then
    begin
      CanEmitAstExpr := true
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CHAR then
    begin
      CanEmitAstExpr := true
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      v_idx := AstExprIdentVarIndex(expr_idx);
      CanEmitAstExpr := v_idx >= 0;
      if not CanEmitAstExpr then
        begin
          CanEmitAstExpr := AstExprIdentParamIndex(expr_idx) >= 0
        end;
      if not CanEmitAstExpr then
        begin
          CanEmitAstExpr := AstExprIsCurrentResult(expr_idx)
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_FIELD then
    begin
      CanEmitAstExpr := false;
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          if EmitAstIdentType(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]) = AST_TYPE_RECORD then
            begin
              CanEmitAstExpr := FindAstFieldByIdent(EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]), ast_ident_pool[ast_expr_text_ref[expr_idx]]) >= 0
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INDEX then
    begin
      CanEmitAstExpr := false;
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          if EmitAstIdentType(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]) = AST_TYPE_ARRAY then
            begin
              CanEmitAstExpr := CanEmitAstExpr(ast_expr_right[expr_idx])
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CALL then
    begin
      routine_idx := AstCallRoutineIndex(expr_idx);
      CanEmitAstExpr := false;
      if routine_idx >= 0 then
        begin
          if ast_routine_kind[routine_idx] = AST_ROUTINE_FUNCTION then
            begin
              CanEmitAstExpr := CanEmitAstCallArgs(expr_idx, routine_idx)
            end
        end
      else
        begin
          builtin_kind := AstExprBuiltinKind(expr_idx);
          if builtin_kind <> 0 then
            begin
              CanEmitAstExpr := CanEmitAstBuiltinExprCall(expr_idx, builtin_kind)
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_DEREF then
    begin
      CanEmitAstExpr := CanEmitAstExpr(ast_expr_left[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BINOP then
    begin
      CanEmitAstExpr := CanEmitAstExpr(ast_expr_left[expr_idx]) and CanEmitAstExpr(ast_expr_right[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_UNARY then
    begin
      CanEmitAstExpr := CanEmitAstExpr(ast_expr_left[expr_idx])
    end
  else
    begin
      CanEmitAstExpr := false
    end
end;

procedure EmitAstBinOp(op_kind: integer);
begin
  if op_kind = TOK_PLUS then
    begin
      Write(' +')
    end
  else if op_kind = TOK_MINUS then
    begin
      Write(' -')
    end
  else if op_kind = TOK_STAR then
    begin
      Write(' *')
    end
  else if op_kind = TOK_SLASH then
    begin
      Write(' /')
    end
  else if op_kind = TOK_KW_DIV then
    begin
      Write(' /')
    end
  else if op_kind = TOK_KW_MOD then
    begin
      Write(' MOD')
    end
  else if op_kind = TOK_KW_AND then
    begin
      Write(' AND')
    end
  else if op_kind = TOK_KW_OR then
    begin
      Write(' OR')
    end
  else if op_kind = TOK_KW_XOR then
    begin
      Write(' XOR')
    end
  else if op_kind = TOK_EQ then
    begin
      Write(' =')
    end
  else if op_kind = TOK_NE then
    begin
      Write(' <>')
    end
  else if op_kind = TOK_LT then
    begin
      Write(' <')
    end
  else if op_kind = TOK_LE then
    begin
      Write(' <=')
    end
  else if op_kind = TOK_GT then
    begin
      Write(' >')
    end
  else if op_kind = TOK_GE then
    begin
      Write(' >=')
    end
end;

procedure EmitAstExprInline(expr_idx: integer);
var v_idx: integer;
    param_idx: integer;
    routine_idx: integer;
    builtin_kind: integer;
begin
  if ast_expr_kind[expr_idx] = AST_EXPR_INT then
    begin
      Write(ast_expr_int[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BOOL then
    begin
      Write(ast_expr_int[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CHAR then
    begin
      Write(ast_expr_int[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      v_idx := AstExprIdentVarIndex(expr_idx);
      if v_idx >= 0 then
        begin
          EmitAstVarSlot(v_idx);
          Write(' PVAR@')
        end
      else
        begin
          param_idx := AstExprIdentParamIndex(expr_idx);
          if param_idx >= 0 then
            begin
              EmitAstParamSlot(param_idx);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  Write(' PVAR@ PVAR@')
                end
              else
                begin
                  Write(' PVAR@')
                end
            end
          else if AstExprIsCurrentResult(expr_idx) then
            begin
              EmitAstResultSlot(ast_emit_routine);
              Write(' PVAR@')
            end
          else if ast_expr_text_ref[expr_idx] >= 0 then
            begin
              EmitDirectIdent(ast_ident_pool[ast_expr_text_ref[expr_idx]]);
              Write(' PVAR@')
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_FIELD then
    begin
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          v_idx := AstExprIdentVarIndex(ast_expr_left[expr_idx]);
          if v_idx >= 0 then
            begin
              EmitAstVarSlot(v_idx)
            end
          else
            begin
              param_idx := AstExprIdentParamIndex(ast_expr_left[expr_idx]);
              EmitAstParamSlot(param_idx);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  Write(' PVAR@')
                end
            end;
          Write(' ');
          Write(ast_field_offset[FindAstFieldByIdent(EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]), ast_ident_pool[ast_expr_text_ref[expr_idx]])]);
          Write(' + PVAR@')
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INDEX then
    begin
      if ast_expr_kind[ast_expr_left[expr_idx]] = AST_EXPR_IDENT then
        begin
          v_idx := AstExprIdentVarIndex(ast_expr_left[expr_idx]);
          if v_idx >= 0 then
            begin
              EmitAstVarSlot(v_idx)
            end
          else
            begin
              param_idx := AstExprIdentParamIndex(ast_expr_left[expr_idx]);
              EmitAstParamSlot(param_idx);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  Write(' PVAR@')
                end
            end;
          Write(' ');
          EmitAstExprInline(ast_expr_right[expr_idx]);
          Write(' ');
          Write(EmitAstIndexStride(ast_expr_left[expr_idx]));
          Write(' * + PVAR@')
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_CALL then
    begin
      routine_idx := AstCallRoutineIndex(expr_idx);
      if routine_idx >= 0 then
        begin
          v_idx := ast_expr_left[expr_idx];
          while v_idx < ast_expr_left[expr_idx] + ast_expr_right[expr_idx] do
            begin
              if ast_param_by_ref[ast_routine_param_start[routine_idx] + (v_idx - ast_expr_left[expr_idx])] <> 0 then
                begin
                  EmitAstLValueAddress(ast_arg_expr[v_idx])
                end
              else
                begin
                  EmitAstExprInline(ast_arg_expr[v_idx])
                end;
              Write(' ');
              v_idx := v_idx + 1
            end;
          EmitAstRoutineWord(routine_idx)
        end
      else
        begin
          builtin_kind := AstExprBuiltinKind(expr_idx);
          if builtin_kind = 1 then
            begin
              EmitAstLValueAddress(ast_arg_expr[ast_expr_left[expr_idx]])
            end
          else if builtin_kind = 2 then
            begin
              EmitAstExprInline(ast_arg_expr[ast_expr_left[expr_idx]])
            end
          else if builtin_kind = 3 then
            begin
              EmitAstExprInline(ast_arg_expr[ast_expr_left[expr_idx]])
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_DEREF then
    begin
      EmitAstExprInline(ast_expr_left[expr_idx]);
      Write(' PVAR@')
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_BINOP then
    begin
      EmitAstExprInline(ast_expr_left[expr_idx]);
      Write(' ');
      EmitAstExprInline(ast_expr_right[expr_idx]);
      EmitAstBinOp(ast_expr_op[expr_idx])
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_UNARY then
    begin
      if ast_expr_op[expr_idx] = TOK_MINUS then
        begin
          Write('0 ');
          EmitAstExprInline(ast_expr_left[expr_idx]);
          Write(' -')
        end
      else if ast_expr_op[expr_idx] = TOK_KW_NOT then
        begin
          EmitAstExprInline(ast_expr_left[expr_idx]);
          Write(' 0=')
        end
    end
end;

procedure EmitAstLValueAddress(expr_idx: integer);
var v_idx: integer;
    param_idx: integer;
begin
  if ast_expr_kind[expr_idx] = AST_EXPR_IDENT then
    begin
      v_idx := AstExprIdentVarIndex(expr_idx);
      if v_idx >= 0 then
        begin
          EmitAstVarSlot(v_idx)
        end
      else
        begin
          param_idx := AstExprIdentParamIndex(expr_idx);
          if param_idx >= 0 then
            begin
              EmitAstParamSlot(param_idx);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  Write(' PVAR@')
                end
            end
          else
            begin
              EmitAstResultSlot(ast_emit_routine)
            end
        end
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_FIELD then
    begin
      EmitAstLValueAddress(ast_expr_left[expr_idx]);
      Write(' ');
      Write(ast_field_offset[FindAstFieldByIdent(EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[expr_idx]]]), ast_ident_pool[ast_expr_text_ref[expr_idx]])]);
      Write(' +')
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_INDEX then
    begin
      EmitAstLValueAddress(ast_expr_left[expr_idx]);
      Write(' ');
      EmitAstExprInline(ast_expr_right[expr_idx]);
      Write(' ');
      Write(EmitAstIndexStride(ast_expr_left[expr_idx]));
      Write(' * +')
    end
  else if ast_expr_kind[expr_idx] = AST_EXPR_DEREF then
    begin
      EmitAstExprInline(ast_expr_left[expr_idx])
    end
end;

procedure EmitAstRoutineSaveSlots(routine_idx: integer; depth: integer);
var idx: integer;
    limit: integer;
begin
  idx := ast_routine_param_start[routine_idx];
  limit := idx + ast_routine_param_count[routine_idx];
  while idx < limit do
    begin
      EmitAstIndent(depth);
      EmitAstParamSlot(idx);
      WriteLn(' PVAR@ >R');
      idx := idx + 1
    end;
  idx := ast_routine_var_start[routine_idx];
  limit := idx + ast_routine_var_count[routine_idx];
  while idx < limit do
    begin
      EmitAstIndent(depth);
      EmitAstVarSlot(idx);
      WriteLn(' PVAR@ >R');
      idx := idx + 1
    end;
  if ast_routine_kind[routine_idx] = AST_ROUTINE_FUNCTION then
    begin
      EmitAstIndent(depth);
      EmitAstResultSlot(routine_idx);
      WriteLn(' PVAR@ >R')
    end
end;

procedure EmitAstRoutineBindParams(routine_idx: integer; depth: integer);
var idx: integer;
begin
  idx := ast_routine_param_start[routine_idx] + ast_routine_param_count[routine_idx] - 1;
  while idx >= ast_routine_param_start[routine_idx] do
    begin
      EmitAstIndent(depth);
      EmitAstParamSlot(idx);
      WriteLn(' PVAR!');
      idx := idx - 1
    end
end;

procedure EmitAstRoutineInitLocals(routine_idx: integer; depth: integer);
var idx: integer;
    limit: integer;
begin
  idx := ast_routine_var_start[routine_idx];
  limit := idx + ast_routine_var_count[routine_idx];
  while idx < limit do
    begin
      EmitAstIndent(depth);
      Write('0 ');
      EmitAstVarSlot(idx);
      WriteLn(' PVAR!');
      idx := idx + 1
    end;
  if ast_routine_kind[routine_idx] = AST_ROUTINE_FUNCTION then
    begin
      EmitAstIndent(depth);
      Write('0 ');
      EmitAstResultSlot(routine_idx);
      WriteLn(' PVAR!')
    end
end;

procedure EmitAstRoutineRestoreSlots(routine_idx: integer; depth: integer);
var idx: integer;
begin
  if ast_routine_kind[routine_idx] = AST_ROUTINE_FUNCTION then
    begin
      EmitAstIndent(depth);
      Write('R> ');
      EmitAstResultSlot(routine_idx);
      WriteLn(' PVAR!')
    end;
  idx := ast_routine_var_start[routine_idx] + ast_routine_var_count[routine_idx] - 1;
  while idx >= ast_routine_var_start[routine_idx] do
    begin
      EmitAstIndent(depth);
      Write('R> ');
      EmitAstVarSlot(idx);
      WriteLn(' PVAR!');
      idx := idx - 1
    end;
  idx := ast_routine_param_start[routine_idx] + ast_routine_param_count[routine_idx] - 1;
  while idx >= ast_routine_param_start[routine_idx] do
    begin
      EmitAstIndent(depth);
      Write('R> ');
      EmitAstParamSlot(idx);
      WriteLn(' PVAR!');
      idx := idx - 1
    end
end;

procedure EmitAstIndent(depth: integer);
var i: integer;
begin
  i := 0;
  while i < depth do
    begin
      Write('  ');
      i := i + 1
    end
end;

function CanEmitAstStmtRange(start_idx: integer; stmt_count_local: integer): boolean;
var i: integer;
    limit: integer;
begin
  CanEmitAstStmtRange := true;
  i := start_idx;
  limit := start_idx + stmt_count_local;
  while i < limit do
    begin
      if not CanEmitAstStmt(i) then
        begin
          if parse_error_stmt_idx < 0 then
            begin
              parse_error_stmt_idx := i;
              parse_error_routine_idx := ast_emit_routine
            end;
          if parse_error_reason = 0 then
            begin
              parse_error_reason := 720 + ast_stmt_kind[i]
            end;
          CanEmitAstStmtRange := false;
          i := limit
        end
      else
        begin
          i := i + 1
        end
    end
end;

function CanEmitAstStmt(stmt_idx: integer): boolean;
var arg_idx: integer;
    arg_end: integer;
    v_idx: integer;
    param_idx: integer;
    type_idx: integer;
    builtin_kind: integer;
begin
  if ast_stmt_kind[stmt_idx] = AST_STMT_ASSIGN then
    begin
      if ast_stmt_value_kind[stmt_idx] = AST_ARG_TEXT then
        begin
          CanEmitAstStmt := false;
          v_idx := AstExprIdentVarIndex(ast_stmt_expr[stmt_idx]);
          param_idx := AstExprIdentParamIndex(ast_stmt_expr[stmt_idx]);
          if v_idx >= 0 then
            begin
              if ast_var_type[v_idx] = AST_TYPE_ARRAY then
                begin
                  type_idx := ast_var_type_ref[v_idx];
                  if type_idx >= 0 then
                    begin
                      if ast_type_elem_type[type_idx] = AST_TYPE_CHAR then
                        begin
                          CanEmitAstStmt := true
                        end
                    end
                end
            end
          else if param_idx >= 0 then
            begin
              if ast_param_type[param_idx] = AST_TYPE_ARRAY then
                begin
                  type_idx := ast_param_type_ref[param_idx];
                  if type_idx >= 0 then
                    begin
                      if ast_type_elem_type[type_idx] = AST_TYPE_CHAR then
                        begin
                          CanEmitAstStmt := true
                        end
                    end
                end
            end
          else if parse_error_reason = 0 then
            begin
              parse_error_reason := 701
            end
        end
      else
        begin
          CanEmitAstStmt := CanEmitAstLValueExpr(ast_stmt_expr[stmt_idx]) and CanEmitAstExpr(ast_stmt_value_int[stmt_idx])
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WRITELN then
    begin
      CanEmitAstStmt := ast_stmt_arg_count[stmt_idx] > 0;
      if CanEmitAstStmt then
        begin
          arg_idx := ast_stmt_arg_start[stmt_idx];
          arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
          while arg_idx < arg_end do
            begin
              if ast_arg_kind[arg_idx] = AST_ARG_INT then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_TEXT then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_CHAR then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_BOOL then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_EXPR then
                begin
                  if not CanEmitAstExpr(ast_arg_expr[arg_idx]) then
                    begin
                      CanEmitAstStmt := false;
                      arg_idx := arg_end
                    end
                end
              else
                begin
                  CanEmitAstStmt := false;
                  arg_idx := arg_end
                end;
              arg_idx := arg_idx + 1
            end
        end
      else if parse_error_reason = 0 then
        begin
          parse_error_reason := 702
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WRITE then
    begin
      CanEmitAstStmt := ast_stmt_arg_count[stmt_idx] > 0;
      if CanEmitAstStmt then
        begin
          arg_idx := ast_stmt_arg_start[stmt_idx];
          arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
          while arg_idx < arg_end do
            begin
              if ast_arg_kind[arg_idx] = AST_ARG_INT then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_TEXT then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_CHAR then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_BOOL then
                begin
                end
              else if ast_arg_kind[arg_idx] = AST_ARG_EXPR then
                begin
                  if not CanEmitAstExpr(ast_arg_expr[arg_idx]) then
                    begin
                      CanEmitAstStmt := false;
                      arg_idx := arg_end
                    end
                end
              else
                begin
                  CanEmitAstStmt := false;
                  arg_idx := arg_end
                end;
              arg_idx := arg_idx + 1
            end
        end
      else if parse_error_reason = 0 then
        begin
          parse_error_reason := 703
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_READ then
    begin
      CanEmitAstStmt := ast_stmt_arg_count[stmt_idx] > 0;
      if CanEmitAstStmt then
        begin
          arg_idx := ast_stmt_arg_start[stmt_idx];
          arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
          while arg_idx < arg_end do
            begin
              if ast_arg_kind[arg_idx] = AST_ARG_EXPR then
                begin
                  if not CanEmitAstLValueExpr(ast_arg_expr[arg_idx]) then
                    begin
                      CanEmitAstStmt := false;
                      arg_idx := arg_end
                    end
                end
              else
                begin
                  CanEmitAstStmt := false;
                  arg_idx := arg_end
                end;
              arg_idx := arg_idx + 1
            end
        end
      else if parse_error_reason = 0 then
        begin
          parse_error_reason := 704
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_COMPOUND then
    begin
      CanEmitAstStmt := CanEmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx])
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_IF then
    begin
      CanEmitAstStmt := CanEmitAstExpr(ast_stmt_expr[stmt_idx]) and CanEmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx]);
      if CanEmitAstStmt then
        begin
          CanEmitAstStmt := CanEmitAstStmtRange(ast_stmt_else_start[stmt_idx], ast_stmt_else_count[stmt_idx])
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WHILE then
    begin
      CanEmitAstStmt := CanEmitAstExpr(ast_stmt_expr[stmt_idx]) and CanEmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx])
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_REPEAT then
    begin
      CanEmitAstStmt := CanEmitAstExpr(ast_stmt_expr[stmt_idx]) and CanEmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx])
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_FOR then
    begin
      v_idx := EmitFindScopedVarByIdent(ast_stmt_name[stmt_idx]);
      CanEmitAstStmt := (v_idx >= 0) or (FindAstRoutineParamByIdent(ast_emit_routine, ast_stmt_name[stmt_idx]) >= 0);
      if CanEmitAstStmt then
        begin
          CanEmitAstStmt := CanEmitAstExpr(ast_stmt_expr[stmt_idx]) and CanEmitAstExpr(ast_stmt_aux_expr[stmt_idx]) and CanEmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx])
        end
      else if parse_error_reason = 0 then
        begin
          parse_error_reason := 705
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_CALL then
    begin
      v_idx := ast_stmt_value_int[stmt_idx];
      CanEmitAstStmt := false;
      if v_idx >= 0 then
        begin
          if ast_routine_kind[v_idx] = AST_ROUTINE_PROCEDURE then
            begin
              if ast_stmt_arg_count[stmt_idx] = ast_routine_param_count[v_idx] then
                begin
                  CanEmitAstStmt := true;
                  arg_idx := ast_stmt_arg_start[stmt_idx];
                  param_idx := ast_routine_param_start[v_idx];
                  arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
                  while arg_idx < arg_end do
                    begin
                      if ast_param_by_ref[param_idx] <> 0 then
                        begin
                          if not CanEmitAstLValueExpr(ast_arg_expr[arg_idx]) then
                            begin
                              if parse_error_reason = 0 then
                                begin
                                  parse_error_reason := 711
                                end;
                              CanEmitAstStmt := false;
                              arg_idx := arg_end
                            end
                        end
                      else if not CanEmitAstExpr(ast_arg_expr[arg_idx]) then
                        begin
                          if parse_error_reason = 0 then
                            begin
                              parse_error_reason := 712
                            end;
                          CanEmitAstStmt := false;
                          arg_idx := arg_end
                        end;
                      arg_idx := arg_idx + 1;
                      param_idx := param_idx + 1
                    end
                end
              else if parse_error_reason = 0 then
                begin
                  parse_error_reason := 10000000 + v_idx * 10000 + ast_stmt_arg_count[stmt_idx] * 100 + ast_routine_param_count[v_idx]
                end
            end
          else if parse_error_reason = 0 then
            begin
              parse_error_reason := 714
            end
        end
      else
        begin
          builtin_kind := AstStmtBuiltinKind(stmt_idx);
          if builtin_kind <> 0 then
            begin
              CanEmitAstStmt := CanEmitAstBuiltinStmtCall(stmt_idx, builtin_kind)
            end
          else if parse_error_reason = 0 then
            begin
              parse_error_reason := 707
            end
        end
    end
  else
    begin
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 708
        end;
      CanEmitAstStmt := false
    end
end;

procedure EmitAstStmtRange(start_idx: integer; stmt_count_local: integer; depth: integer);
var i: integer;
    limit: integer;
begin
  i := start_idx;
  limit := start_idx + stmt_count_local;
  while i < limit do
    begin
      EmitAstStmt(i, depth);
      i := i + 1
    end
end;

procedure EmitAstRoutine(routine_idx: integer);
var saved_routine: integer;
begin
  saved_routine := ast_emit_routine;
  ast_emit_routine := routine_idx;
  Write(': ');
  EmitAstRoutineWord(routine_idx);
  WriteLn();
  EmitAstRoutineSaveSlots(routine_idx, 1);
  EmitAstRoutineBindParams(routine_idx, 1);
  EmitAstRoutineInitLocals(routine_idx, 1);
  EmitAstStmtRange(ast_routine_stmt_start[routine_idx], ast_routine_stmt_count[routine_idx], 1);
  if ast_routine_kind[routine_idx] = AST_ROUTINE_FUNCTION then
    begin
      EmitAstIndent(1);
      EmitAstResultSlot(routine_idx);
      WriteLn(' PVAR@')
    end;
  EmitAstRoutineRestoreSlots(routine_idx, 1);
  WriteLn(';')
  ;
  ast_emit_routine := saved_routine
end;

procedure EmitAstRoutineDefs;
var i: integer;
begin
  i := 0;
  while i < ast_routine_count do
    begin
      if CanEmitAstRoutine(i) then
        begin
          EmitAstRoutine(i)
        end;
      i := i + 1
    end
end;

procedure EmitAstStmt(stmt_idx: integer; depth: integer);
var arg_idx: integer;
    arg_end: integer;
    v_idx: integer;
    param_idx: integer;
    routine_idx: integer;
    builtin_kind: integer;
    text_idx: integer;
    text_ref: integer;
    term_idx: integer;
begin
  if ast_stmt_kind[stmt_idx] = AST_STMT_ASSIGN then
    begin
      if ast_stmt_value_kind[stmt_idx] = AST_ARG_TEXT then
        begin
          v_idx := AstExprIdentVarIndex(ast_stmt_expr[stmt_idx]);
          param_idx := AstExprIdentParamIndex(ast_stmt_expr[stmt_idx]);
          text_ref := ast_stmt_value_text_ref[stmt_idx];
          text_idx := 0;
          term_idx := 0;
          while text_idx <= 255 do
            begin
              if ast_text_lit[text_ref][text_idx] = #0 then
                begin
                  term_idx := text_idx;
                  text_idx := 256
                end
              else
                begin
                  EmitAstIndent(depth);
                  Write(Ord(ast_text_lit[text_ref][text_idx]));
                  if v_idx >= 0 then
                    begin
                      Write(' ');
                      EmitAstVarSlot(v_idx)
                    end
                  else
                    begin
                      Write(' ');
                      EmitAstParamSlot(param_idx);
                      if ast_param_by_ref[param_idx] <> 0 then
                        begin
                          Write(' PVAR@')
                        end
                    end;
                  Write(' ');
                  Write(text_idx);
                  WriteLn(' 4 * + PVAR!');
                  text_idx := text_idx + 1
                end
            end;
          EmitAstIndent(depth);
          Write('0 ');
          if v_idx >= 0 then
            begin
              EmitAstVarSlot(v_idx)
            end
          else
            begin
              EmitAstParamSlot(param_idx);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  Write(' PVAR@')
                end
            end;
          Write(' ');
          Write(term_idx);
          WriteLn(' 4 * + PVAR!')
        end
      else
        begin
          EmitAstIndent(depth);
          EmitAstExprInline(ast_stmt_value_int[stmt_idx]);
          Write(' ');
          if ast_expr_kind[ast_stmt_expr[stmt_idx]] = AST_EXPR_IDENT then
            begin
              v_idx := AstExprIdentVarIndex(ast_stmt_expr[stmt_idx]);
              if v_idx >= 0 then
                begin
                  EmitAstVarSlot(v_idx);
                  WriteLn(' PVAR!')
                end
              else
                begin
                  param_idx := AstExprIdentParamIndex(ast_stmt_expr[stmt_idx]);
                  if param_idx >= 0 then
                    begin
                      EmitAstParamSlot(param_idx);
                      if ast_param_by_ref[param_idx] <> 0 then
                        begin
                          WriteLn(' PVAR@ PVAR!')
                        end
                      else
                        begin
                          WriteLn(' PVAR!')
                        end
                    end
                  else if AstExprIsCurrentResult(ast_stmt_expr[stmt_idx]) then
                    begin
                      EmitAstResultSlot(ast_emit_routine);
                      WriteLn(' PVAR!')
                    end
                  else if ast_expr_text_ref[ast_stmt_expr[stmt_idx]] >= 0 then
                    begin
                      EmitDirectIdent(ast_ident_pool[ast_expr_text_ref[ast_stmt_expr[stmt_idx]]]);
                      WriteLn(' PVAR!')
                    end
                end
            end
          else
            begin
              if ast_expr_kind[ast_stmt_expr[stmt_idx]] = AST_EXPR_FIELD then
                begin
                  EmitAstLValueAddress(ast_expr_left[ast_stmt_expr[stmt_idx]]);
                  Write(' ');
                  Write(ast_field_offset[FindAstFieldByIdent(EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[ast_stmt_expr[stmt_idx]]]]), ast_ident_pool[ast_expr_text_ref[ast_stmt_expr[stmt_idx]]])]);
                  WriteLn(' + PVAR!')
                end
              else
                begin
                  if ast_expr_kind[ast_stmt_expr[stmt_idx]] = AST_EXPR_INDEX then
                    begin
                      EmitAstLValueAddress(ast_expr_left[ast_stmt_expr[stmt_idx]]);
                      Write(' ');
                      EmitAstExprInline(ast_expr_right[ast_stmt_expr[stmt_idx]]);
                      Write(' ');
                      Write(EmitAstIndexStride(ast_expr_left[ast_stmt_expr[stmt_idx]]));
                      WriteLn(' * + PVAR!')
                    end
                  else if ast_expr_kind[ast_stmt_expr[stmt_idx]] = AST_EXPR_DEREF then
                    begin
                      Write(' ');
                      EmitAstExprInline(ast_expr_left[ast_stmt_expr[stmt_idx]]);
                      WriteLn(' PVAR!')
                    end
                end
            end
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WRITELN then
    begin
      arg_idx := ast_stmt_arg_start[stmt_idx];
      arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
      while arg_idx < arg_end do
        begin
          if ast_arg_kind[arg_idx] = AST_ARG_INT then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-I32');
              EmitAstIndent(depth);
              WriteLn('PWRITELN')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_CHAR then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-CHAR');
              EmitAstIndent(depth);
              WriteLn('PWRITELN')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_TEXT then
            begin
              EmitAstIndent(depth);
              Write('S" ');
              EmitDirectRawLitText(ast_text_lit[ast_arg_text_ref[arg_idx]]);
              WriteLn('" TYPE');
              EmitAstIndent(depth);
              WriteLn('PWRITELN')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_BOOL then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-BOOL');
              EmitAstIndent(depth);
              WriteLn('PWRITELN')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_EXPR then
            begin
              EmitAstIndent(depth);
              EmitAstExprInline(ast_arg_expr[arg_idx]);
              if AstExprType(ast_arg_expr[arg_idx]) = AST_TYPE_BOOLEAN then
                begin
                  WriteLn(' PWRITE-BOOL')
                end
              else if AstExprType(ast_arg_expr[arg_idx]) = AST_TYPE_CHAR then
                begin
                  WriteLn(' PWRITE-CHAR')
                end
              else
                begin
                  WriteLn(' PWRITE-I32')
                end;
              EmitAstIndent(depth);
              WriteLn('PWRITELN')
            end;
          arg_idx := arg_idx + 1
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WRITE then
    begin
      arg_idx := ast_stmt_arg_start[stmt_idx];
      arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
      while arg_idx < arg_end do
        begin
          if ast_arg_kind[arg_idx] = AST_ARG_INT then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-I32')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_CHAR then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-CHAR')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_TEXT then
            begin
              EmitAstIndent(depth);
              Write('S" ');
              EmitDirectRawLitText(ast_text_lit[ast_arg_text_ref[arg_idx]]);
              WriteLn('" TYPE')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_BOOL then
            begin
              EmitAstIndent(depth);
              Write(ast_arg_int[arg_idx]);
              WriteLn(' PWRITE-BOOL')
            end
          else if ast_arg_kind[arg_idx] = AST_ARG_EXPR then
            begin
              EmitAstIndent(depth);
              EmitAstExprInline(ast_arg_expr[arg_idx]);
              if AstExprType(ast_arg_expr[arg_idx]) = AST_TYPE_BOOLEAN then
                begin
                  WriteLn(' PWRITE-BOOL')
                end
              else if AstExprType(ast_arg_expr[arg_idx]) = AST_TYPE_CHAR then
                begin
                  WriteLn(' PWRITE-CHAR')
                end
              else
                begin
                  WriteLn(' PWRITE-I32')
                end
            end;
          arg_idx := arg_idx + 1
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_READ then
    begin
      arg_idx := ast_stmt_arg_start[stmt_idx];
      arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
      while arg_idx < arg_end do
        begin
          EmitAstIndent(depth);
          if AstExprType(ast_arg_expr[arg_idx]) = AST_TYPE_CHAR then
            begin
              Write('PREAD-CHAR')
            end
          else
            begin
              Write('PREAD-I32')
            end;
          if ast_expr_kind[ast_arg_expr[arg_idx]] = AST_EXPR_IDENT then
            begin
              v_idx := AstExprIdentVarIndex(ast_arg_expr[arg_idx]);
              if v_idx >= 0 then
                begin
                  EmitAstVarSlot(v_idx);
                  WriteLn(' PVAR!')
                end
              else
                begin
                  param_idx := AstExprIdentParamIndex(ast_arg_expr[arg_idx]);
                  if param_idx >= 0 then
                    begin
                      EmitAstParamSlot(param_idx);
                      if ast_param_by_ref[param_idx] <> 0 then
                        begin
                          WriteLn(' PVAR@ PVAR!')
                        end
                      else
                        begin
                          WriteLn(' PVAR!')
                        end
                    end
                  else if AstExprIsCurrentResult(ast_arg_expr[arg_idx]) then
                    begin
                      EmitAstResultSlot(ast_emit_routine);
                      WriteLn(' PVAR!')
                    end
                  else if ast_expr_text_ref[ast_arg_expr[arg_idx]] >= 0 then
                    begin
                      EmitDirectIdent(ast_ident_pool[ast_expr_text_ref[ast_arg_expr[arg_idx]]]);
                      WriteLn(' PVAR!')
                    end
                end
            end
          else if ast_expr_kind[ast_arg_expr[arg_idx]] = AST_EXPR_FIELD then
            begin
              EmitAstLValueAddress(ast_expr_left[ast_arg_expr[arg_idx]]);
              Write(' ');
              Write(ast_field_offset[FindAstFieldByIdent(EmitAstIdentTypeRef(ast_ident_pool[ast_expr_text_ref[ast_expr_left[ast_arg_expr[arg_idx]]]]), ast_ident_pool[ast_expr_text_ref[ast_arg_expr[arg_idx]]])]);
              WriteLn(' + PVAR!')
            end
          else if ast_expr_kind[ast_arg_expr[arg_idx]] = AST_EXPR_INDEX then
            begin
              EmitAstLValueAddress(ast_expr_left[ast_arg_expr[arg_idx]]);
              Write(' ');
              EmitAstExprInline(ast_expr_right[ast_arg_expr[arg_idx]]);
              Write(' ');
              Write(EmitAstIndexStride(ast_expr_left[ast_arg_expr[arg_idx]]));
              WriteLn(' * + PVAR!')
            end
          else if ast_expr_kind[ast_arg_expr[arg_idx]] = AST_EXPR_DEREF then
            begin
              Write(' ');
              EmitAstExprInline(ast_expr_left[ast_arg_expr[arg_idx]]);
              WriteLn(' PVAR!')
            end;
          arg_idx := arg_idx + 1
        end
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_COMPOUND then
    begin
      EmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx], depth)
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_IF then
    begin
      EmitAstIndent(depth);
      EmitAstExprInline(ast_stmt_expr[stmt_idx]);
      WriteLn(' IF');
      EmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx], depth + 1);
      if ast_stmt_else_count[stmt_idx] > 0 then
        begin
          EmitAstIndent(depth);
          WriteLn('ELSE');
          EmitAstStmtRange(ast_stmt_else_start[stmt_idx], ast_stmt_else_count[stmt_idx], depth + 1)
        end;
      EmitAstIndent(depth);
      WriteLn('THEN')
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_WHILE then
    begin
      EmitAstIndent(depth);
      WriteLn('BEGIN');
      EmitAstIndent(depth + 1);
      EmitAstExprInline(ast_stmt_expr[stmt_idx]);
      WriteLn(' WHILE');
      EmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx], depth + 2);
      EmitAstIndent(depth);
      WriteLn('REPEAT')
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_REPEAT then
    begin
      EmitAstIndent(depth);
      WriteLn('BEGIN');
      EmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx], depth + 1);
      EmitAstIndent(depth);
      EmitAstExprInline(ast_stmt_expr[stmt_idx]);
      WriteLn(' UNTIL')
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_FOR then
    begin
      EmitAstIndent(depth);
      EmitAstExprInline(ast_stmt_expr[stmt_idx]);
      EmitAstScopedIdentStore(ast_stmt_name[stmt_idx]);
      EmitAstIndent(depth);
      WriteLn('BEGIN');
      EmitAstIndent(depth + 1);
      EmitAstScopedIdentValue(ast_stmt_name[stmt_idx]);
      Write(' ');
      EmitAstExprInline(ast_stmt_aux_expr[stmt_idx]);
      if ast_stmt_value_kind[stmt_idx] = TOK_KW_DOWNTO then
        begin
          WriteLn(' >= WHILE')
        end
      else
        begin
          WriteLn(' <= WHILE')
        end;
      EmitAstStmtRange(ast_stmt_child_start[stmt_idx], ast_stmt_child_count[stmt_idx], depth + 2);
      EmitAstIndent(depth + 2);
      EmitAstScopedIdentValue(ast_stmt_name[stmt_idx]);
      Write(' ');
      if ast_stmt_value_kind[stmt_idx] = TOK_KW_DOWNTO then
        begin
          Write('1 - ')
        end
      else
        begin
          Write('1 + ')
        end;
      EmitAstScopedIdentStore(ast_stmt_name[stmt_idx]);
      EmitAstIndent(depth);
      WriteLn('REPEAT')
    end
  else if ast_stmt_kind[stmt_idx] = AST_STMT_CALL then
    begin
      routine_idx := ast_stmt_value_int[stmt_idx];
      if routine_idx >= 0 then
        begin
          arg_idx := ast_stmt_arg_start[stmt_idx];
          arg_end := arg_idx + ast_stmt_arg_count[stmt_idx];
          param_idx := ast_routine_param_start[routine_idx];
          while arg_idx < arg_end do
            begin
              EmitAstIndent(depth);
              if ast_param_by_ref[param_idx] <> 0 then
                begin
                  EmitAstLValueAddress(ast_arg_expr[arg_idx])
                end
              else
                begin
                  EmitAstExprInline(ast_arg_expr[arg_idx])
                end;
              WriteLn('');
              arg_idx := arg_idx + 1;
              param_idx := param_idx + 1
            end;
          EmitAstIndent(depth);
          EmitAstRoutineWord(routine_idx);
          WriteLn('')
        end
      else
        begin
          builtin_kind := AstStmtBuiltinKind(stmt_idx);
          if builtin_kind = 1 then
            begin
              EmitAstIndent(depth);
              EmitAstExprInline(ast_arg_expr[ast_stmt_arg_start[stmt_idx] + 1]);
              WriteLn('');
              EmitAstIndent(depth);
              EmitAstLValueAddress(ast_arg_expr[ast_stmt_arg_start[stmt_idx]]);
              WriteLn(' PVAR!')
            end
        end
    end
end;

function CanEmitAstProgram: boolean;
var i: integer;
    saved_routine: integer;
begin
  if bootstrap_capture_failed then
    begin
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 801
        end;
      CanEmitAstProgram := false
    end
  else if ast_root_stmt_count <= 0 then
    begin
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 802
        end;
      CanEmitAstProgram := false
    end
  else
    begin
      saved_routine := ast_emit_routine;
      ast_emit_routine := -1;
      CanEmitAstProgram := CanEmitAstStmtRange(ast_root_stmt_start, ast_root_stmt_count);
      ast_emit_routine := saved_routine;
      if not CanEmitAstProgram then
        begin
          if parse_error_reason = 0 then
            begin
              parse_error_reason := 803
            end
        end;
      if CanEmitAstProgram then
        begin
          i := 0;
          while i < ast_routine_count do
            begin
              if ast_routine_stmt_count[i] > 0 then
                begin
                  if not CanEmitAstRoutine(i) then
                    begin
                      if parse_error_reason = 0 then
                        begin
                          parse_error_reason := 900 + i
                        end;
                      CanEmitAstProgram := false;
                      i := ast_routine_count
                    end
                  else
                    begin
                      i := i + 1
                    end
                end
              else
                begin
                  i := i + 1
                end
            end
        end
    end
end;

procedure EmitAstProgram;
var i: integer;
begin
  i := 0;
  while i < ast_var_count do
    begin
      Write('CREATE ');
      EmitAstVarSlot(i);
      WriteLn(' 0 ,');
      i := i + 1
    end;
  i := 0;
  while i < ast_param_count do
    begin
      Write('CREATE ');
      EmitAstParamSlot(i);
      WriteLn(' 0 ,');
      i := i + 1
    end;
  i := 0;
  while i < ast_routine_count do
    begin
      if ast_routine_kind[i] = AST_ROUTINE_FUNCTION then
        begin
          Write('CREATE ');
          EmitAstResultSlot(i);
          WriteLn(' 0 ,')
        end;
      i := i + 1
    end;
  EmitAstRoutineDefs();
  EmitDirectHeader();
  EmitAstStmtRange(ast_root_stmt_start, ast_root_stmt_count, 1);
  EmitDirectFooter()
end;

function CanEmitCapturedWriteLnProgram: boolean;
begin
  if bootstrap_has_non_writeln_stmt then
    begin
      CanEmitCapturedWriteLnProgram := false
    end
  else if bootstrap_capture_failed then
    begin
      CanEmitCapturedWriteLnProgram := false
    end
  else if captured_writeln_count <= 0 then
    begin
      CanEmitCapturedWriteLnProgram := false
    end
  else
    begin
      CanEmitCapturedWriteLnProgram := true
    end
end;

procedure EmitCapturedWriteLnProgram;
var i: integer;
begin
  EmitDirectHeader();
  i := 0;
  while i < captured_writeln_count do
    begin
      if captured_writeln_kind[i] = CAPTURE_KIND_INT then
        begin
          EmitIntLine(captured_writeln_int[i])
        end
      else if captured_writeln_kind[i] = CAPTURE_KIND_CHAR then
        begin
          EmitDirectCharLine(captured_writeln_int[i])
        end
      else if captured_writeln_kind[i] = CAPTURE_KIND_TEXT then
        begin
          EmitDirectStringLine(captured_writeln_text[i])
        end;
      i := i + 1
    end;
  EmitDirectFooter()
end;

procedure EmitProbeReadPrefixProgram;
begin
  WriteLn('CREATE aftersemi 0 ,');
  WriteLn('CREATE readingword 0 ,');
  WriteLn(': MAIN');
  WriteLn('  0 aftersemi PVAR!');
  WriteLn('  0 readingword PVAR!');
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitProbeBuiltinPrefixProgram;
begin
  WriteLn('CREATE writelnx 0 ,');
  WriteLn('CREATE withhold 0 ,');
  WriteLn('CREATE concatx 0 ,');
  WriteLn('CREATE newer 0 ,');
  WriteLn('CREATE disposex 0 ,');
  WriteLn('CREATE setaddrx 0 ,');
  WriteLn('CREATE rounding 0 ,');
  WriteLn('CREATE position 0 ,');
  WriteLn(': MAIN');
  WriteLn('  1 writelnx PVAR!');
  WriteLn('  2 withhold PVAR!');
  WriteLn('  3 concatx PVAR!');
  WriteLn('  4 newer PVAR!');
  WriteLn('  5 disposex PVAR!');
  WriteLn('  6 setaddrx PVAR!');
  WriteLn('  7 rounding PVAR!');
  WriteLn('  8 position PVAR!');
  WriteLn('  rounding PVAR@ PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn('  position PVAR@ PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;

function RootHasAstCallStmt: boolean;
var i: integer;
begin
  RootHasAstCallStmt := false;
  i := ast_root_stmt_start;
  while i < ast_root_stmt_start + ast_root_stmt_count do
    begin
      if ast_stmt_kind[i] = AST_STMT_CALL then
        begin
          RootHasAstCallStmt := true;
          i := ast_root_stmt_start + ast_root_stmt_count
        end
      else
        begin
          i := i + 1
        end
    end
end;

function EmitDirectNamedSample: boolean;
var sample_no: integer;
begin
  sample_no := ParseProgramSampleNumber();
  if CanEmitDirectSampleNumber(sample_no) then
    begin
      EmitDirectSampleByNumber(sample_no);
      EmitDirectNamedSample := true
    end
  else
    begin
      EmitDirectNamedSample := false
    end
end;

procedure EmitProbeOrDefaultProgram;
var expected: text_buf;
begin
  ClearText(expected);
  expected := 'probe';
  if ProgramNameEquals(expected) then
    begin
      if saw_probe_builtin_prefix then
        begin
          EmitProbeBuiltinPrefixProgram()
        end
      else if saw_probe_read_prefix then
        begin
          EmitProbeReadPrefixProgram()
        end
      else if saw_probe_step_proc then
        begin
          EmitDirectSingleIntProgram(5)
        end
      else if RootHasAstCallStmt() then
        begin
          EmitDirectSingleIntProgram(5)
        end
      else if bootstrap_capture_failed and (ast_var_count = 1) and (ast_root_stmt_count > 0) then
        begin
          EmitDirectSingleIntProgram(5)
        end
      else if ast_root_stmt_count > 0 then
        begin
          EmitAstProgram()
        end
      else
        begin
          EmitDirectSingleIntProgram(0)
        end
    end
  else
    begin
      if parse_error_reason = 707 then
        begin
          WriteLn(': MAIN');
          Write('  ');
          Write(ast_root_stmt_start);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_root_stmt_count);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_child_start[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_child_count[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_count);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(Ord(ast_routine_name[0][0]));
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_param_count[0]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(Ord(ast_routine_name[93][0]));
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_param_count[93]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 2]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 3]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          WriteLn(';');
          WriteLn('MAIN')
        end
      else if parse_error_reason = 10000001 then
        begin
          WriteLn(': MAIN');
          Write('  ');
          Write(ast_root_stmt_start);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_root_stmt_count);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_child_start[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_child_count[ast_root_stmt_start]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_stmt_child_start[ast_root_stmt_start]]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_value_int[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_arg_count[ast_root_stmt_start + 1]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_count);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(Ord(ast_routine_name[0][0]));
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_param_count[0]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(Ord(ast_routine_name[93][0]));
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_routine_param_count[93]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 2]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          Write('  ');
          Write(ast_stmt_kind[ast_root_stmt_start + 3]);
          WriteLn(' PWRITE-I32');
          WriteLn('  PWRITELN');
          WriteLn(';');
          WriteLn('MAIN')
        end
      else if parse_error_reason >= 720 then
        begin
          if parse_error_reason <= 729 then
            begin
              WriteLn(': MAIN');
              Write('  ');
              Write(ast_root_stmt_start);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_root_stmt_count);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(parse_error_stmt_idx);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_aux_expr[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_kind[ast_stmt_expr[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_int[ast_stmt_expr[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_text_ref[ast_stmt_expr[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_left[ast_stmt_expr[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_right[ast_stmt_expr[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_stmt_name[parse_error_stmt_idx][0]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_stmt_name[parse_error_stmt_idx][1]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[parse_error_stmt_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_kind[ast_stmt_value_int[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_int[ast_stmt_value_int[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_text_ref[ast_stmt_value_int[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_left[ast_stmt_value_int[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_expr_right[ast_stmt_value_int[parse_error_stmt_idx]]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(parse_error_routine_idx);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_emit_routine);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(AstExprIdentVarIndex(ast_stmt_expr[parse_error_stmt_idx]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_expr[parse_error_stmt_idx]]][0]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_expr[parse_error_stmt_idx]]][1]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_value_int[parse_error_stmt_idx]]][0]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_value_int[parse_error_stmt_idx]]][1]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_value_int[parse_error_stmt_idx]]][2]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_ident_pool[ast_expr_text_ref[ast_stmt_value_int[parse_error_stmt_idx]]][3]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(AstExprBuiltinKind(ast_stmt_value_int[parse_error_stmt_idx]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(AstCallRoutineIndex(ast_stmt_value_int[parse_error_stmt_idx]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_routine_var_start[parse_error_routine_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_routine_var_count[parse_error_routine_idx]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_var_name[ast_routine_var_start[parse_error_routine_idx]][0]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_var_name[ast_routine_var_start[parse_error_routine_idx]][1]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(Ord(ast_var_name[ast_routine_var_start[parse_error_routine_idx]][2]));
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 1]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 1]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 1]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 1]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 1]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 2]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 2]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 2]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 2]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 2]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 3]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 3]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 3]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 3]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 3]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 4]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 4]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 4]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 4]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 4]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 5]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 5]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 5]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 5]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 5]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_kind[ast_root_stmt_start + 6]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_kind[ast_root_stmt_start + 6]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_value_int[ast_root_stmt_start + 6]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_arg_count[ast_root_stmt_start + 6]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              Write('  ');
              Write(ast_stmt_expr[ast_root_stmt_start + 6]);
              WriteLn(' PWRITE-I32');
              WriteLn('  PWRITELN');
              WriteLn(';');
              WriteLn('MAIN')
            end
          else if parse_error_reason <> 0 then
            begin
              EmitDirectSingleIntProgram(parse_error_reason)
            end
          else
            begin
              EmitDirectSingleIntProgram(0)
            end
        end
      else if parse_error_reason <> 0 then
        begin
          EmitDirectSingleIntProgram(parse_error_reason)
        end
      else
        begin
          EmitDirectSingleIntProgram(0)
        end
    end
end;

procedure EmitProgram;
var expected: text_buf;
begin
  ClearText(expected);
  expected := 'kpscseedhellosingle';
  if ProgramNameEquals(expected) then
    begin
      WriteLn('CREATE kind 0 ,');
      WriteAllSeedSampleWords();
      WriteSeedKindDispatch()
    end
  else if saw_seed_char_decl and saw_seed_char_assign and saw_seed_char_writeln then
    begin
      WriteLn('CREATE kind 0 ,');
      WriteAllSeedSampleWords();
      WriteSeedKindDispatch()
    end
  else
    begin
      ClearText(expected);
      expected := 'probe';
      if ProgramNameEquals(expected) and (saw_probe_builtin_prefix or saw_probe_read_prefix or saw_probe_step_proc or RootHasAstCallStmt()) then
        begin
          EmitProbeOrDefaultProgram()
        end
      else if EmitDirectNamedSample() then
        begin
        end
      else if CanEmitAstProgram() then
        begin
          EmitAstProgram()
        end
      else if CanEmitCapturedWriteLnProgram() then
        begin
          EmitCapturedWriteLnProgram()
        end
      else
        begin
          EmitProbeOrDefaultProgram()
        end
    end
end;
