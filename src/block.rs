pub enum BlockType {
    Plain,
    Basic,
    Graph,
    Copy,
    Goto,
    MultiGoto,
    List,
    Condition,
    If,
    WhileDo,
    DoWhile,
    Switch,
    InfLoop
}

pub trait FlowBlock {
    fn as_flow_block(&self) -> &dyn FlowBlock;
}

pub trait BlockCopy: FlowBlock {
}

pub trait BlockGoto: FlowBlock {
}

pub trait BlockMultiGoto: FlowBlock {
}

pub trait BlockList: FlowBlock {
}

pub trait BlockCond: FlowBlock {
}

pub trait BlockIfGoto: FlowBlock {
}

pub trait BlockIf: FlowBlock {
}

pub trait BlockIfElse: FlowBlock {
}

pub trait BlockWhileDo: FlowBlock {
}

pub trait BlockDoWhile: FlowBlock {
}

pub trait BlockInfLoop: FlowBlock {
}

pub trait BlockSwitch: FlowBlock {
}


pub trait BlockGraph {
    fn as_flow_block(&self) -> &dyn FlowBlock;

    fn new_block(&mut self) -> &dyn FlowBlock;
    fn new_block_copy(&mut self, block: &dyn FlowBlock) -> &dyn BlockCopy;
    fn new_block_goto(&mut self, block: &dyn FlowBlock) -> &dyn BlockGoto;
    fn new_block_multi_goto(&mut self, block: &dyn FlowBlock, out_edge: i32) -> &dyn BlockMultiGoto;
    fn new_block_list(&mut self, blocks: &[&dyn FlowBlock]) -> &dyn BlockList;
    fn new_block_cond(&mut self, b1: &dyn FlowBlock, b2: &dyn FlowBlock) -> &dyn BlockCond;
    fn new_block_if_goto(&mut self, cond: &dyn FlowBlock) -> &dyn BlockIfGoto;
    fn new_block_if(&mut self, cond: &dyn FlowBlock, block: &dyn FlowBlock) -> &dyn BlockIf;
    fn new_block_if_else(&mut self, cond: &dyn FlowBlock, true_case: &dyn FlowBlock, false_case: &dyn FlowBlock) -> &dyn BlockIfElse;
    fn new_block_while_do(&mut self, cond: &dyn FlowBlock, block: &dyn FlowBlock) -> &dyn BlockWhileDo;
    fn new_block_do_while(&mut self, cond: &dyn FlowBlock) -> &dyn BlockDoWhile;
    fn new_block_inf_loop(&mut self, body: &dyn FlowBlock) -> &dyn BlockInfLoop;
    fn new_block_switch(&mut self, cases: &[&dyn FlowBlock], has_exit: bool) -> &dyn BlockSwitch;
}