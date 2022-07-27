using System;
using System.Collections.Generic;
using System.Linq;
using de4dot.blocks;
using de4dot.blocks.cflow;
using de4dot.code.deobfuscators.ConfuserEx.x86;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

namespace de4dot.code.deobfuscators.ConfuserEx
{
    internal class ControlFlowFixer : IBlocksDeobfuscator
    {
        public bool ExecuteIfNotModified { get; } = false;
        public List<MethodDef> NativeMethods = new List<MethodDef>();

        private readonly InstructionEmulator _instructionEmulator = new InstructionEmulator();

        private Blocks _blocks;
        private Local _switchKey;

        private int? CalculateKey(SwitchData switchData)
        {
            var popValue = _instructionEmulator.Peek();
            if (popValue == null || !popValue.IsInt32() || !(popValue as Int32Value).AllBitsValid())
                return null;

            _instructionEmulator.Pop();
            var num = ((Int32Value)popValue).Value;

            if (switchData is NativeSwitchData)
            {
                var nativeSwitchData = (NativeSwitchData)switchData;
                var nativeMethod = new X86Method(nativeSwitchData.NativeMethodDef, _blocks.Method.Module as ModuleDefMD); //TODO: Possible null
                return nativeMethod.Execute(num);
            }
            if (switchData is NormalSwitchData)
            {
                var normalSwitchData = (NormalSwitchData)switchData;
                return num ^ normalSwitchData.Key.Value;
            }
            return null;
        }

        private int? CalculateSwitchCaseIndex(Block block, SwitchData switchData, int key)
        {
            if (switchData is NativeSwitchData)
            {
                _instructionEmulator.Push(new Int32Value(key));
                _instructionEmulator.Emulate(block.Instructions, block.SwitchData.IsKeyHardCoded ? 2 : 1, block.Instructions.Count - 1);

                var popValue = _instructionEmulator.Peek();
                _instructionEmulator.Pop();
                return ((Int32Value)popValue).Value;
            }
            if (switchData is NormalSwitchData)
            {
                var normalSwitchData = (NormalSwitchData)switchData;
                return key % normalSwitchData.DivisionKey;
            }
            return null;
        }

        private void ProcessHardcodedSwitch(Block switchBlock) // a single-case switch
        {
            var targets = switchBlock.Targets;
            _instructionEmulator.Push(new Int32Value(switchBlock.SwitchData.Key.Value));

            var key = CalculateKey(switchBlock.SwitchData);
            if (!key.HasValue)
                throw new Exception("CRITICAL ERROR: KEY HAS NO VALUE");

            var switchCaseIndex = CalculateSwitchCaseIndex(switchBlock, switchBlock.SwitchData, key.Value);
            if (!switchCaseIndex.HasValue)
                throw new Exception("CRITICAL ERROR: SWITCH CASE HAS NO VALUE");
            if (targets.Count < switchCaseIndex)
                throw new Exception("CRITICAL ERROR: KEY OUT OF RANGE");

            var targetBlock = targets[switchCaseIndex.Value];
            targetBlock.SwitchData.Key = key;

            switchBlock.Instructions.Clear();
            switchBlock.ReplaceLastNonBranchWithBranch(0, targetBlock);
        }

        private void ProcessBlock(List<Block> switchFallThroughs, Block switchCaseBlock, Block switchBlock)
        {
            var targets = switchBlock.Targets;
            _instructionEmulator.Emulate(switchCaseBlock.Instructions, 0, switchCaseBlock.Instructions.Count);

            if (_instructionEmulator.Peek().IsUnknown())
                throw new Exception("CRITICAL ERROR: STACK VALUE UNKNOWN");

            var key = CalculateKey(switchBlock.SwitchData);
            if (!key.HasValue)
                throw new Exception("CRITICAL ERROR: KEY HAS NO VALUE");

            var switchCaseIndex = CalculateSwitchCaseIndex(switchBlock, switchBlock.SwitchData, key.Value);
            if (!switchCaseIndex.HasValue)
                throw new Exception("CRITICAL ERROR: SWITCH CASE HAS NO VALUE");
            if (targets.Count < switchCaseIndex)
                throw new Exception("CRITICAL ERROR: KEY OUT OF RANGE");

            var targetBlock = targets[switchCaseIndex.Value];
            targetBlock.SwitchData.Key = key;

            switchCaseBlock.Add(new Instr(OpCodes.Pop.ToInstruction())); // neutralize the arithmetics and leave de4dot to remove them
            switchCaseBlock.ReplaceLastNonBranchWithBranch(0, targetBlock);

            ProcessFallThroughs(switchFallThroughs, switchBlock, targetBlock, key.Value);
            switchCaseBlock.Processed = true;
        }

        private void ProcessTernaryBlock(List<Block> switchCaseBlocks, Block ternaryBlock, Block switchBlock)
        {
            var targets = switchBlock.Targets;

            for (var i = 0; i < 2; i++) // loop both source blocks 
            {
                var sourceBlock = ternaryBlock.Sources[0];

                if(ternaryBlock.SwitchData.Key.HasValue) // single instruction: pop -- no key!
                    SetLocalSwitchKey(ternaryBlock.SwitchData.Key.Value); // set old key for both iterations!

                _instructionEmulator.Emulate(sourceBlock.Instructions, 0, sourceBlock.Instructions.Count);
                _instructionEmulator.Emulate(ternaryBlock.Instructions, 0, ternaryBlock.Instructions.Count);

                if (_instructionEmulator.Peek().IsUnknown())
                    throw new Exception("CRITICAL ERROR: STACK VALUE UNKNOWN");

                var key = CalculateKey(switchBlock.SwitchData);
                if (!key.HasValue)
                    throw new Exception("CRITICAL ERROR: KEY HAS NO VALUE");

                var switchCaseIndex = CalculateSwitchCaseIndex(switchBlock, switchBlock.SwitchData, key.Value);
                if (!switchCaseIndex.HasValue)
                    throw new Exception("CRITICAL ERROR: SWITCH CASE HAS NO VALUE");
                if (targets.Count < switchCaseIndex)
                    throw new Exception("CRITICAL ERROR: KEY OUT OF RANGE");

                var targetBlock = targets[switchCaseIndex.Value];
                targetBlock.SwitchData.Key = key;

                sourceBlock.Instructions[sourceBlock.Instructions.Count - 1] = new Instr(OpCodes.Pop.ToInstruction());
                sourceBlock.ReplaceLastNonBranchWithBranch(0, targets[switchCaseIndex.Value]);

                ProcessFallThroughs(switchCaseBlocks, switchBlock, targets[switchCaseIndex.Value], key.Value);
                // the second source block now becomes the first one
            }

            //switchCaseBlock.Instructions.Clear();
            ternaryBlock.Add(new Instr(OpCodes.Pop.ToInstruction())); // don't add pop before both iterations have finished
            ternaryBlock.Processed = true;
        }

    
        public void DeobfuscateBegin(Blocks blocks)
        {
            _blocks = blocks;
            _instructionEmulator.Initialize(_blocks, true);
        }

        public bool Deobfuscate(List<Block> methodBlocks)
        {
            var switchBlocks = GetSwitchBlocks(methodBlocks); // blocks that contain a switch
            var modifications = 0;

            foreach (var switchBlock in switchBlocks)
            {
                if (switchBlock.SwitchData.IsKeyHardCoded)
                {
                    ProcessHardcodedSwitch(switchBlock);
                    modifications++;
                    continue;
                }

                _switchKey = Instr.GetLocalVar(_blocks.Locals,
                    switchBlock.Instructions[switchBlock.Instructions.Count - 4]);

                if (DeobfuscateSwitchBlock(methodBlocks, switchBlock))
                    modifications++;
            }
            return modifications > 0;
        }

        private bool DeobfuscateSwitchBlock(List<Block> methodBlocks, Block switchBlock)
        {
            var switchFallThroughs = methodBlocks.FindAll(b => b.FallThrough == switchBlock); // blocks that fallthrough to the switch block
            _instructionEmulator.Initialize(_blocks, true); //TODO: Remove temporary precaution

            var blocksLeft = switchFallThroughs.Count; //  how many blocks left to proccess
            var blockIndex = 0; // block that sets the first switch destination
            var failedCount = 0;

            while (blocksLeft > 0)
            {
                if (blockIndex > switchFallThroughs.Count - 1)
                    blockIndex = 0;

                if (failedCount > switchFallThroughs.Count)
                {
                    Console.WriteLine("Some blocks couldn't be processed!");
                    break;
                }

                var switchCaseBlock = switchFallThroughs[blockIndex];
                if (switchCaseBlock.Processed)
                {
                    blockIndex++;
                    continue;
                }

                if (NeedSwitchKey(switchCaseBlock))
                {
                    if (!switchCaseBlock.SwitchData.Key.HasValue)
                    {
                        failedCount++;
                        blockIndex++;
                        continue;
                    }
                    SetLocalSwitchKey(switchCaseBlock.SwitchData.Key.Value);
                }

                if (switchCaseBlock.IsTernary()) {
                    ProcessTernaryBlock(switchFallThroughs, switchCaseBlock, switchBlock);
                }
                else {
                    ProcessBlock(switchFallThroughs, switchCaseBlock, switchBlock);
                }

                failedCount = 0;
                blocksLeft--;
                blockIndex++;
            }

            if (blocksLeft == switchFallThroughs.Count) // Have we modified anything?
                return false;

            return true;
        }


        public bool IsConfuserExSwitchBlock(Block block)
        {
            if (block.LastInstr.OpCode.Code != Code.Switch || ((Instruction[])block.LastInstr.Operand)?.Length == 0)
                return false;

            var instructions = block.Instructions;
            var lastIndex = instructions.Count - 1;

            
            if (instructions.Count < 4)
                return false;
            if (!instructions[lastIndex - 3].IsStloc())
                return false;
            if (!instructions[lastIndex - 2].IsLdcI4())
                return false;
            if (instructions[lastIndex - 1].OpCode != OpCodes.Rem_Un)
                return false;
            
            var nativeSwitchData = new NativeSwitchData(block);
            if (nativeSwitchData.Initialize())
            {
                block.SwitchData = nativeSwitchData;
                if (!NativeMethods.Contains(nativeSwitchData.NativeMethodDef)) // add for remove
                    NativeMethods.Add(nativeSwitchData.NativeMethodDef);
                return true;
            }

            var normalSwitchData = new NormalSwitchData(block);
            if (normalSwitchData.Initialize())
            {
                block.SwitchData = normalSwitchData;
                return true;
            }

            return false;
        }

        public List<Block> GetSwitchBlocks(List<Block> blocks) // get the blocks which contain the switch statement
        {
            var switchBlocks = new List<Block>();

            foreach (var block in blocks)
                if (IsConfuserExSwitchBlock(block))
                    switchBlocks.Add(block);

            return switchBlocks;
        }


        private readonly List<Block> _processedFallThroughs = new List<Block>();

        // add the switch key to all appropriate fallthroughs
        private void ProcessFallThroughs(List<Block> switchCaseBlocks, Block switchBlock, Block targetBlock, int switchKey)
        {
            DoProcessFallThroughs(switchCaseBlocks, switchBlock, targetBlock, switchKey);
            _processedFallThroughs.Clear();
        }

        private void DoProcessFallThroughs(List<Block> switchCaseBlocks, Block switchBlock, Block targetBlock, int switchKey)
        {
            if (_processedFallThroughs.Contains(targetBlock))
                return;
            _processedFallThroughs.Add(targetBlock);

            if (targetBlock.FallThrough == switchBlock && switchCaseBlocks.Contains(targetBlock) && !targetBlock.SwitchData.Key.HasValue)
                targetBlock.SwitchData.Key = switchKey;

            var fallThrough = targetBlock.FallThrough;
            if (fallThrough == null)
                return;

            if (fallThrough.LastInstr.OpCode != OpCodes.Ret && fallThrough != switchBlock)
                DoProcessFallThroughs(switchCaseBlocks, switchBlock, fallThrough, switchKey);

            if (targetBlock.CountTargets() > 1)
                foreach (var targetBlockTarget in targetBlock.Targets)
                {
                    if (targetBlockTarget == switchBlock)
                        return;
                    DoProcessFallThroughs(switchCaseBlocks, switchBlock, targetBlockTarget, switchKey);
                }
        }


        private bool NeedSwitchKey(Block block)
        {
            foreach (var instr in block.Instructions)
                if (instr.IsLdloc() && Instr.GetLocalVar(_blocks.Locals, instr) == _switchKey)
                    return true;
            return false;
        }

        private int? GetSwitchKey()
        {
            var val = _instructionEmulator.GetLocal(_switchKey);
            if (!val.IsInt32())
                return null;
            var value = val as Int32Value;
            if (value == null || !value.AllBitsValid())
                return null;
            return value.Value;
        }

        private void SetLocalSwitchKey(int key)
        {
            _instructionEmulator.SetLocal(_switchKey, new Int32Value(key));
        }
    }
}
