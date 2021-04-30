#include <stdio.h>
#include <string.h>

#include "dufs.h"
#include "filesystem.h"
#include "util.h"

int main(void) {
    util_init("disk.bin", 1 << 20);
    // fs_format();

    // uint8_t buf[131072];

    // inodeptr_t r = dufs_dir_find_filename(&inode, "test");

    // // size_t r = dufs_inode_read_data(&inode, 0, 8704, buf);
    // fprintf(stderr, "%u\n", r);

    u8 buf[8192];

    for (size_t i = 0; i < 8192; i++) {
        buf[i] = (i / 2) ^ 0x00;
    }

    struct inode_t inode;
    dufs_read_inode(&inode, dufs_root_inode_pos());

    dufs_inode_write_data(&inode, 0, 8192, buf);
    dufs_inode_write_data(&inode, 8192, 8192, buf);

    // size_t r = dufs_write_datablock(128, 266, 11, buf);
    // fprintf(stderr, "%lu\n", r);

    // dufs_bitmap_set_datablock(20, false);

    // fwrite(buf, r, 1, stdout);

    // file_t *fd;
    // fd = fs_creat("/test.txt");
    // fs_write(fd, (uint8_t *)"Hello, world!", 12);
    // fs_close(fd);

    util_end();
}
