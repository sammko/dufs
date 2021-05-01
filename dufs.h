#ifndef DUFS_H
#define DUFS_H

#include "filesystem.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define SECTORS_PER_DATABLOCK 4
#define DATABLOCK_SIZE (SECTOR_SIZE * SECTORS_PER_DATABLOCK)
#define DATABLOCK_INDIR_PTR_COUNT (DATABLOCK_SIZE / sizeof(blockptr_t))

#define BITS_PER_SECTOR (SECTOR_SIZE * 8)
#define SUPERBLOCK_POS 0
#define BITMAP_OFFSET 1

#define INODE_REF_COUNT 16
#define INODE_INDIR_COUNT 3
#define INODE_TYPE_FILE STAT_TYPE_FILE
#define INODE_TYPE_DIR STAT_TYPE_DIR
#define INODE_TYPE_SYMLINK STAT_TYPE_SYMLINK

#define MAX_FILENAME_LEN 255
#define MAX_PATH_LEN 2048

#define DPTR_VALID(p) (p) // use 0 for invalid

#define FILET_INODEPTR 0
#define FILET_OFFSET 1

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int32_t blockptr_t;
typedef int32_t inodeptr_t;

struct inode_t {
    u16 refcnt;
    u8 type;
    u8 _pad0;
    u32 fsize;
    u32 num;
    u32 data[INODE_REF_COUNT];
    u32 data_indir[INODE_INDIR_COUNT];
} __attribute__((packed, scalar_storage_order("little-endian")));

struct superblock_t {
    u32 last_inode_ptr;
} __attribute__((packed, scalar_storage_order("little-endian")));

struct direntry_t {
    u32 inode;
    u16 entry_size;
    // u8 filename_length;
    char filename[]; // fam
} __attribute__((packed, scalar_storage_order("little-endian")));

struct datablock_indir_t {
    blockptr_t pts[DATABLOCK_INDIR_PTR_COUNT];
} __attribute__((packed, scalar_storage_order("little-endian")));

_Static_assert(sizeof(struct inode_t) <= SECTOR_SIZE, "inode too big");
_Static_assert(sizeof(struct datablock_indir_t) == DATABLOCK_SIZE,
               "datablock size wrong");

size_t dufs_bitmap_sectors();
void dufs_bitmap_set_datablock(size_t pos, bool state);
size_t dufs_first_usable_sector();
inodeptr_t dufs_root_inode_pos();

size_t dufs_read_datablock(size_t datablock, size_t offset, size_t len,
                           u8 *outbuf);
size_t dufs_read_datablock_indirect(int indir, size_t dblock_indir,
                                    size_t offset, size_t len, u8 *outbuf);
void dufs_read_inode(struct inode_t *in, size_t sector_addr);
size_t dufs_inode_read_data(const struct inode_t *in, size_t from, size_t len,
                            u8 *buf);
inodeptr_t dufs_dir_find_filename(const struct inode_t *dir,
                                  const char *filename);
size_t dufs_write_datablock(size_t dblock, size_t offset, size_t len,
                            const u8 *buf);
size_t dufs_write_datablock_indirect(int indir, size_t dblock_indir,
                                     size_t offset, size_t len, const u8 *buf);
size_t dufs_inode_write_data(struct inode_t *in, size_t from, size_t len,
                             const u8 *buf);
void dufs_dir_append_filename(struct inode_t *dir, const char *filename,
                              inodeptr_t target);
#endif