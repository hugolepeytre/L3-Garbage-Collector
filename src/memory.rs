use crate::{L3Value, LOG2_VALUE_BYTES};

const HEADER_SIZE : usize = 1;
const MIN_BLOCK_SIZE : usize = 1;
const TAG_NONE : i32 = 255;
const NULL_POINTER : i32 = usize::MAX as i32;
const N_FREE_LISTS : usize = 32;

pub struct Memory {
    content: Vec<L3Value>,
    bitmap_ix: usize,
    bitmap_size : usize,
    free_list_ix: usize,
    blocks_begin_ix: usize,
    top_frames: [usize; 2]
}

fn ix_to_addr(index: usize) -> L3Value {
    (index << LOG2_VALUE_BYTES) as L3Value
}

fn addr_to_ix(addr: L3Value) -> usize {
    debug_assert!(addr & ((1 << LOG2_VALUE_BYTES) - 1) == 0,
                    "invalid address: {} (16#{:x})", addr, addr);
    (addr >> LOG2_VALUE_BYTES) as usize
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            bitmap_ix: 0,
            bitmap_size: 0,
            free_list_ix: 0,
            blocks_begin_ix: 0,
            top_frames: [0, 0]
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        self.bitmap_ix = heap_start_index;
        let heap_size = self.content.len() - heap_start_index;
        // Division rounding up, by 33 so size is 1/32nd of the rest of the heap
        self.bitmap_size = heap_size/33 + (heap_size % 33 != 0) as usize; 
        self.free_list_ix = self.bitmap_ix + self.bitmap_size;
        self.blocks_begin_ix = self.free_list_ix + N_FREE_LISTS;

        let first_block_ix = self.blocks_begin_ix + HEADER_SIZE;
        let free_list_ix = self.free_list_ix;
        for i in 0..N_FREE_LISTS {
            self[free_list_ix + i] = NULL_POINTER;
        }
        self[free_list_ix + N_FREE_LISTS - 1] = first_block_ix as L3Value;
        let first_block_size = self.content.len() - first_block_ix;
        self.set_block_header(first_block_ix, TAG_NONE, first_block_size);
        self[first_block_ix] = NULL_POINTER;

        self.top_frames[0] = heap_start_index - 258;
        self.top_frames[1] = self.top_frames[0] - 259;
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize)
                    -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);

        let target_size = if (size as usize) < MIN_BLOCK_SIZE {MIN_BLOCK_SIZE} else {size as usize};
        let block = self.find_free_block(target_size, root);
        let allocated_size = self.split_free_block(block, target_size);
        
        self.set_bit(block, 1);
        self.set_block_header(block, tag, allocated_size);
        block
    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block) as i32;
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) { self[copy + i] = self[block + i] };
        copy
    }

    pub fn free(&mut self, block: usize) {
        if self.check_bit(block, 1) {
            self.set_block_tag(block, TAG_NONE);
            self.set_bit(block, 0);
            self.add_free_block(block);
        }
    }

    pub fn collect_garbage(&mut self, root: usize) {
        debug_assert!(self.assert_free_list_valid());
        debug_assert!(self.assert_bitmap_valid());
        self.mark(root, true);
        self.sweep();
        debug_assert!(self.assert_free_list_valid());
        debug_assert!(self.assert_bitmap_valid());
    }

    pub fn mark(&mut self, block: usize, is_root: bool) {
        if !is_root {
            debug_assert!(self.assert_allocated(block));
            self.set_bit(block, 0);
        }
        let size = self.block_size(block) as usize;
        for i in 0..size {
            let maybe_addr = self[block + i];
            if maybe_addr & ((1 << LOG2_VALUE_BYTES) - 1) == 0 {
                let pointer = addr_to_ix(maybe_addr);
                if pointer == self.top_frames[0] || pointer == self.top_frames[1] {
                    self.mark(pointer, true);
                }
                if self.assert_valid_header(pointer) && self.check_bit(pointer, 1) {
                    self.mark(pointer, false);
                }
            }
        }
    }

    pub fn sweep(&mut self) {
        let mut back_pointers = vec![self.free_list_ix; N_FREE_LISTS];
        let mut block = self.blocks_begin_ix + HEADER_SIZE;
        for i in 0..N_FREE_LISTS {
            back_pointers[i] += i;
            self[back_pointers[i]] = NULL_POINTER;
        }
        while block < self.content.len() {
            debug_assert!(self.assert_valid_header(block));
            let tag = self.block_tag(block);
            if tag == TAG_NONE {
                debug_assert!(self.assert_unallocated(block));
                let size = self.block_size(block) as usize;
                let next_block = block + size + HEADER_SIZE;
                if next_block >= self.content.len() {return}
                let next_tag = self.block_tag(next_block);
                let newly_free = self.check_bit(next_block, 1);
                if next_tag == TAG_NONE || newly_free {
                    if newly_free {
                        self.set_bit(next_block, 0);
                    }
                    let new_size = self.block_size(next_block) as usize + HEADER_SIZE + size;
                    self.set_block_size(block, new_size);
                }
                else {
                    let selected_list = if size < N_FREE_LISTS {size} else {N_FREE_LISTS} - 1;
                    self[back_pointers[selected_list]] = block as i32;
                    self[block] = NULL_POINTER;
                    back_pointers[selected_list] = block;
                    block = next_block;
                }
            }
            else if self.check_bit(block, 0) {
                self.set_bit(block, 1);
                debug_assert!(self.assert_allocated(block));
                block = block + self.block_size(block) as usize + HEADER_SIZE;
            }
            else {
                self.set_block_tag(block, TAG_NONE);
                self.set_bit(block, 0);
            }
        }
    }

    pub fn block_tag(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] & 0xFF
    }

    pub fn block_size(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] >> 8
    }

    pub fn set_block_header(&mut self, block: usize, tag: L3Value, size: usize) {
        self[block - HEADER_SIZE] = ((size as L3Value) << 8) | tag
    }

    pub fn set_block_tag(&mut self, block: usize, tag: L3Value) {
        self[block - HEADER_SIZE] = (self.block_size(block) << 8) | tag
    }

    pub fn set_block_size(&mut self, block: usize, size: usize) {
        self[block - HEADER_SIZE] = ((size as i32) << 8) | self.block_tag(block);
    }

    pub fn find_free_block(&mut self, size: usize, root: usize) -> usize {
        debug_assert!(size > 0);
        let mut selected_free_list = if size < N_FREE_LISTS {size} else {N_FREE_LISTS} - 1;
        let mut back_pointer = self.free_list_ix + selected_free_list;
        let mut gc_called = false;

        loop {
            debug_assert!(self.free_list_ix <= back_pointer);
            let next_block = self[back_pointer] as usize;
            if next_block as i32 == NULL_POINTER {
                if selected_free_list < N_FREE_LISTS - 1 {
                    selected_free_list = N_FREE_LISTS - 1;
                    back_pointer = self.free_list_ix + selected_free_list;
                }
                else {
                    if gc_called {
                        panic!("no more memory");
                    }
                    self.collect_garbage(root);
                    gc_called = true;
                    selected_free_list = if size < N_FREE_LISTS {size} else {N_FREE_LISTS} - 1;
                    back_pointer = self.free_list_ix +selected_free_list;
                }
            }
            else if self.block_size(next_block as usize) >= size as i32 {
                self.remove_free_block(next_block, back_pointer);
                debug_assert!(self.assert_unallocated(next_block));
                return next_block
            }
            else {
                back_pointer = next_block;
            }
        }
    }

    pub fn split_free_block(&mut self, block: usize, target_size: usize) -> usize {
        debug_assert!(self.assert_unallocated(block));
        debug_assert!(target_size >= MIN_BLOCK_SIZE);
        let b_size = self.block_size(block) as usize;
        debug_assert!(target_size <= b_size);

        if b_size >= target_size + HEADER_SIZE + MIN_BLOCK_SIZE {
            let split_block = block + target_size + HEADER_SIZE;
            let split_size = b_size - target_size - HEADER_SIZE;
            self.set_block_header(split_block, TAG_NONE, split_size);
            self.add_free_block(split_block);
            target_size
        }
        else {
            b_size
        }
    }

    pub fn set_bit(&mut self, block: usize, new_bit: L3Value) {
        debug_assert!(self.assert_valid_header(block));
        debug_assert!(self.check_bit(block, 1 - new_bit));
        let (mem_ix, bit_ix) = self.get_bit_ix(block);
        // Actually just flips the bit, because we should never set a bit to its current value
        self[mem_ix] = self[mem_ix] ^ (1 << bit_ix);
    }

    pub fn get_bit(&self, block: usize) -> i32 {
        debug_assert!(self.assert_valid_header(block));
        let (mem_ix, bit_ix) = self.get_bit_ix(block);
        (self[mem_ix] >> bit_ix) & 1
    }
    
    pub fn get_bit_ix(&self, block: usize) -> (usize, usize) {
        let offset = block - self.blocks_begin_ix;
        let mem_idx = self.bitmap_ix + offset/32;
        debug_assert!(self.bitmap_ix <= mem_idx && mem_idx < self.bitmap_ix + self.bitmap_size);
        (mem_idx, offset%32)
    }

    pub fn add_free_block(&mut self, block: usize) {
        debug_assert!(self.assert_unallocated(block), "Trying to add free block of address {}, size {}", block, self.block_size(block));
        let size = self.block_size(block) as usize;
        let selected_list = if size < N_FREE_LISTS { size } else { N_FREE_LISTS } - 1;
        let free_list_ix = self.free_list_ix + selected_list;
        self[block] = self[free_list_ix];
        self[free_list_ix] = block as i32;
    }

    pub fn remove_free_block(&mut self, block: usize, back_pointer: usize) {
        debug_assert!(self.assert_unallocated(block));
        debug_assert!(self[back_pointer] as usize == block);
        self[back_pointer] = self[block];
    }

    pub fn assert_valid_header(&self, block: usize) -> bool {
        if block < self.content.len() {
            block >= self.blocks_begin_ix + HEADER_SIZE && self.block_size(block) >= MIN_BLOCK_SIZE as i32
        }
        else {
            false
        }
    }

    pub fn assert_tag_none(&self, block: usize) -> bool {
        self.assert_valid_header(block) && self.block_tag(block) == TAG_NONE
    }

    pub fn assert_tag_not_none(&self, block: usize) -> bool {
        self.assert_valid_header(block) && self.block_tag(block) != TAG_NONE
    }

    pub fn assert_unallocated(&self, block: usize) -> bool {
        self.assert_tag_none(block) && self.check_bit(block, 0)
    }

    pub fn assert_allocated(&self, block: usize) -> bool {
        self.assert_tag_not_none(block) && self.check_bit(block, 1)
    }

    pub fn check_bit(&self, block: usize, bit_check: L3Value) -> bool {
        debug_assert!(self.assert_valid_header(block));
        self.get_bit(block) == bit_check
    }

    pub fn assert_free_list_valid(&self) -> bool {
        let mut result = true;
        for i in 0..N_FREE_LISTS {
            result &= self.assert_single_free_list_valid(i);
        }
        result
    }

    pub fn assert_single_free_list_valid(&self, selected_list: usize) -> bool {
        let mut counter = self.content.len() - self.blocks_begin_ix;
        let mut block = self[self.free_list_ix + selected_list];
        while counter > 0 {
            if block == NULL_POINTER {
                return true
            }
            block = self[block as usize];
            counter -= 1;
        }
        false
    }

    pub fn assert_bitmap_valid(&self) -> bool {
        let mut block = self.blocks_begin_ix + HEADER_SIZE;
        while block < self.content.len() {
            self.assert_valid_header(block);
            let target_bit = if self.block_tag(block) == TAG_NONE {0} else {1};
            if !self.check_bit(block, target_bit) || block + self.block_size(block) as usize > self.content.len() {
                return false
            }
            else {
                block = block + self.block_size(block) as usize + HEADER_SIZE;
            }
        }
        return true
    }

    pub fn debug_print_mem_state(&self) {
        let mut block = self.blocks_begin_ix + HEADER_SIZE;
        let mut count = 0;
        while block < self.content.len() {
            let tag = self.block_tag(block);
            let size = self.block_size(block);
            let bit = self.get_bit(block);
            eprintln!("Block {} has address {}, tag {}, size {} and bit {}\n", count, block, tag, size, bit);
            block = block + size as usize + HEADER_SIZE;
            count += 1;
        }
    }

    pub fn debug_print_free_list(&self) {
        let mut block = self.blocks_begin_ix + HEADER_SIZE;
        let mut count = 0;
        while block as i32 != NULL_POINTER {
            let tag = self.block_tag(block);
            let size = self.block_size(block);
            let bit = self.get_bit(block);
            let next_block = self[block] as usize;
            eprintln!("Block {} has address {}, tag {}, size {} and bit {}, next block {}\n", count, block, tag, size, bit, next_block);
            block = next_block;
            count += 1;
        }
    }
}

use core::panic;
use std::ops::{ Index, IndexMut };

impl Index<usize> for Memory {
    type Output = L3Value;
    fn index(&self, i: usize) -> &Self::Output {
        &self.content[i]
    }
}

impl IndexMut<usize> for Memory {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.content[i]
    }
}
