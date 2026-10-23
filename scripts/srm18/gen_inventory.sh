#!/bin/bash
# Machine-generated part of HSK_INVENTORY.txt: the defining lines (file:line) of every start-state / reset
# candidate, extracted by grep at the current checkout, followed by the hand-written applicability table.
cd "$(dirname "$0")/../.."
echo "SRM18 inventory: start-state candidates (generated $(git rev-parse --short HEAD), grep of definition lines)"
echo "== definitions (file:line:text) =="
for pat in 'def runModuleTG' 'structure KState' 'structure KidState' 'def KT ' 'def KSn' 'def stepModuleTG' \
  'def ResetN ' 'def ResetNk' 'def Reset1' 'def ResetM' 'def kidsInit' 'def kidsZero' 'def resetKT' 'def resetKids' \
  'def ComposedG ' 'def ComposedGW' 'def ComposedNW' 'def SeqChildRunN' 'def RunOn ' 'def Start0' 'def StartVC'; do
  grep -rn --include=*.lean -- "^$pat\|^  *$pat" Tools Sparkle 2>/dev/null | cut -c1-200
done
echo "== instance theorems quantifying s (hrun) over universally quantified start states =="
grep -n "(s : KState (KT" Tests/Compiler/Srm1[1-7]*Test.lean Tests/Compiler/Srm13ParentTest.lean 2>/dev/null | cut -c1-140 | sort -u | head -40
echo "== uses of the Reset parameter in composed statements (count of 'ComposedG .* (ResetNk') =="
grep -rc --include=*.lean "ComposedG (fun D => KSn (childMap D.modules) [0-9n( a-z=]*) (ResetNk" Tools Tests | grep -v ":0" | head -30
echo "== equalities 'kids = ' of start state to a constructed state in Tools/Tests (excluding SRM16/17 corollaries) =="
grep -rn --include=*.lean "s\.kids = \|kids = resetKids\|kids = kidsInit" Tools Tests | grep -v "Srm1[67]" | cut -c1-160
echo "== (none above => no equality-form start-state proposition exists outside SRM16/17) =="
