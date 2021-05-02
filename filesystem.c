#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "dufs.h"
#include "filesystem.h"
#include "util.h"

/**
 * Write inode to disk
 */
void dufs_write_inode(const struct inode_t *in, size_t sector_addr) {
    u8 sector[SECTOR_SIZE] = {0};
    memcpy(sector, in, sizeof(struct inode_t));
    hdd_write(sector_addr, sector);
}

/**
 * Read inode from disk
 */
void dufs_read_inode(struct inode_t *in, size_t sector_addr) {
    u8 sector[SECTOR_SIZE];
    hdd_read(sector_addr, sector);
    memcpy(in, sector, sizeof(struct inode_t));
}

void dufs_write_superblock(const struct superblock_t *sb) {
    u8 sector[SECTOR_SIZE] = {0};
    memcpy(sector, sb, sizeof(struct superblock_t));
    hdd_write(SUPERBLOCK_POS, sector);
}

void dufs_read_superblock(struct superblock_t *sb) {
    u8 sector[SECTOR_SIZE];
    hdd_read(SUPERBLOCK_POS, sector);
    memcpy(sb, sector, sizeof(struct superblock_t));
}

/**
 * How big is the bitmap in sectors
 */
size_t dufs_bitmap_sectors() {
    size_t hdd_sectors = hdd_size() / SECTOR_SIZE;
    size_t bitmap_bytes = (hdd_sectors + 7) / 8;
    return (bitmap_bytes + SECTOR_SIZE - 1) / SECTOR_SIZE;
}

/**
 * Layout on disk:
 * (1) superblock (1 sector)
 * (2) bitmap (dufs_bitmap_sectors)
 * (3) root inode (1 sector)
 * (4) data
 *
 * returns the start of (4) data
 */
size_t dufs_first_usable_sector() {
    return BITMAP_OFFSET + dufs_bitmap_sectors() + 1;
}

inodeptr_t dufs_root_inode_pos() {
    return BITMAP_OFFSET + dufs_bitmap_sectors();
}

/**
 * This should only be called when formatting.
 * Sets bits of the bitmap corresponding to (1) -- (3) in layout.
 * Theoretically not necessary, as they are always guaranteed to be allocated.
 */
void dufs_bitmap_init() {
    // fill everything until first_usable_sector with ones.
    size_t n = dufs_first_usable_sector();
    size_t bytes = n / 8;
    size_t fullsectors = bytes / SECTOR_SIZE;
    u8 ones[SECTOR_SIZE];

    fprintf(stderr, "n: %lu\n", n);

    memset(ones, 0xff, SECTOR_SIZE);
    for (size_t i = 0; i < fullsectors; i++) {
        hdd_write(BITMAP_OFFSET + i, ones);
    }
    size_t bytes_left = bytes % SECTOR_SIZE;
    u8 lastbuf[SECTOR_SIZE] = {0};
    for (size_t i = 0; i < bytes_left; i++) {
        lastbuf[i] = 0xff;
    }

    u8 bits_left = n % 8;
    lastbuf[bytes_left] = (1 << bits_left) - 1;

    hdd_write(BITMAP_OFFSET + fullsectors, lastbuf);
}

/**
 * Set allocated state in the bitmap. pos is index of sector
 */
void dufs_bitmap_set(size_t pos, bool state) {
    size_t sector_addr = BITMAP_OFFSET + pos / BITS_PER_SECTOR;
    size_t sector_off = pos % BITS_PER_SECTOR;
    size_t byte_off = sector_off / 8;
    u8 bit_index = sector_off % 8;

    u8 bit = 1 << bit_index;

    u8 sector[SECTOR_SIZE];
    hdd_read(sector_addr, sector);

    if (state) {
        sector[byte_off] |= bit;
    } else {
        sector[byte_off] &= ~bit;
    }

    hdd_write(sector_addr, sector);
}

/**
 * Set allocated state of datablock in the bitmap. pos is index of datablock
 */
void dufs_bitmap_set_datablock(size_t pos, bool state) {
    _Static_assert(SECTORS_PER_DATABLOCK == 4, "datablock must be 4 sectors");
    size_t fsec = pos * 4;

    size_t sector_addr = BITMAP_OFFSET + fsec / BITS_PER_SECTOR;
    size_t sector_off = fsec % BITS_PER_SECTOR;
    size_t byte_off = sector_off / 8;
    u8 bit_index = (pos % 2) * 4;

    u8 mask = 0xF << bit_index;

    u8 sector[SECTOR_SIZE];
    hdd_read(sector_addr, sector);

    if (state) {
        sector[byte_off] |= mask;
    } else {
        sector[byte_off] &= ~mask;
    }

    hdd_write(sector_addr, sector);
}

/**
 * Get allocated state in the bitmap. pos is index of sector
 */
bool dufs_bitmap_get(size_t pos) {
    size_t sector_addr = BITMAP_OFFSET + pos / BITS_PER_SECTOR;
    size_t sector_off = pos % BITS_PER_SECTOR;
    size_t byte_off = sector_off / 8;
    u8 bit_index = sector_off % 8;

    u8 bit = 1 << bit_index;

    u8 sector[SECTOR_SIZE];
    hdd_read(sector_addr, sector);

    return !!(sector[byte_off] & bit);
}

/**
 * Get allocated state of datablock in the bitmap. pos is index of datablock
 * This returns true if either of the sectors under the datablock is in use.
 */
bool dufs_bitmap_get_datablock(size_t pos) {
    _Static_assert(SECTORS_PER_DATABLOCK == 4, "datablock must be 4 sectors");
    size_t fsec = pos * 4;

    size_t sector_addr = BITMAP_OFFSET + fsec / BITS_PER_SECTOR;
    size_t sector_off = fsec % BITS_PER_SECTOR;
    size_t byte_off = sector_off / 8;
    u8 bit_index = (pos % 2) * 4;
    u8 mask = 0xF << bit_index;

    u8 sector[SECTOR_SIZE];
    hdd_read(sector_addr, sector);

    return !!(sector[byte_off] & mask);
}

blockptr_t dufs_alloc_datablock(size_t req) {
    fprintf(stderr, "alloc data called with req: %lu\n", req);
    if (!dufs_bitmap_get_datablock(req)) {
        // requested block is free, alloc it
        dufs_bitmap_set_datablock(req, true);
        fprintf(stderr, "   req avail\n");
        return req;
    }
    fprintf(stderr, "   req notavail\n");
    size_t count = hdd_size() / DATABLOCK_SIZE;
    // the bitmap really needs a cache
    // TODO maybe start looking at a pseudorandom block instead of in-order
    for (size_t db = 0; db < count; db++) {
        if (!dufs_bitmap_get_datablock(db)) {
            dufs_bitmap_set_datablock(db, true);
            fprintf(stderr, "   ret: %lu\n", db);
            return db;
        }
    }
    return FAIL;
}

inodeptr_t dufs_alloc_inode(size_t req) {
    fprintf(stderr, "alloc inode called with req: %lu\n", req);
    if (!dufs_bitmap_get(req)) {
        dufs_bitmap_set(req, true);
        fprintf(stderr, "   req avail\n");
        return req;
    }
    fprintf(stderr, "   req notavail\n");
    // TODO bitmap cache or randomize
    size_t count = hdd_size() / SECTOR_SIZE;
    for (size_t i = 0; i < count; i++) {
        if (!dufs_bitmap_get(i)) {
            dufs_bitmap_set(i, true);
            fprintf(stderr, "   ret: %lu\n", i);
            return i;
        }
    }
    return FAIL;
}

size_t dufs_read_datablock(size_t dblock, size_t offset, size_t len,
                           u8 *outbuf) {
    fprintf(stderr, "read called with: dblock: %lu, offset: %lu, len: %lu\n",
            dblock, offset, len);

    if (offset >= DATABLOCK_SIZE)
        return 0;

    size_t sector = dblock * SECTORS_PER_DATABLOCK;
    if (len > DATABLOCK_SIZE - offset) {
        len = DATABLOCK_SIZE - offset;
    }
    size_t skip = offset / SECTOR_SIZE;
    size_t sector_offset = offset % SECTOR_SIZE;
    size_t first_len = SECTOR_SIZE - sector_offset;
    fprintf(stderr, "   skip: %lu, sector_offset: %lu, first_len: %lu\n", skip,
            sector_offset, first_len);
    if (len < first_len) {
        first_len = len;
    }
    u8 buf[SECTOR_SIZE];
    hdd_read(sector + skip, buf);
    memcpy(outbuf, buf + sector_offset, first_len);
    outbuf += first_len;

    size_t rem_count = (len - first_len) / SECTOR_SIZE;
    size_t last_len = (len - first_len) % SECTOR_SIZE;
    fprintf(stderr, "   rem_count: %lu, last_len: %lu\n", rem_count, last_len);

    for (size_t i = 0; i < rem_count; i++) {
        hdd_read(sector + skip + i + 1, outbuf);
        // hdd_read(sector + skip + i + 1, buf);
        // memcpy(outbuf, buf, SECTOR_SIZE);
        outbuf += SECTOR_SIZE;
    }

    hdd_read(sector + skip + rem_count + 1, buf);
    memcpy(outbuf, buf, last_len);
    return len;
}

size_t dufs_read_datablock_indirect(int indir, size_t dblock_indir,
                                    size_t offset, size_t len, u8 *outbuf) {
    if (indir == 0) {
        return dufs_read_datablock(dblock_indir, offset, len, outbuf);
    }

    struct datablock_indir_t ptrs;
    dufs_read_datablock(dblock_indir, 0, DATABLOCK_SIZE, (u8 *)&ptrs);

    size_t subblock_size = DATABLOCK_SIZE;
    for (int i = 0; i < indir - 1; i++) {
        subblock_size *= DATABLOCK_INDIR_PTR_COUNT;
    }
    size_t my_size = subblock_size * DATABLOCK_INDIR_PTR_COUNT;
    if (offset >= my_size)
        return 0;
    if (len > my_size - offset) {
        len = my_size - offset;
    }
    size_t tlen = len;

    int iref = offset / subblock_size;
    size_t suboffset = offset % subblock_size;

    size_t rl;
    while (len > 0) {
        size_t readlen = len;
        if (readlen > subblock_size - suboffset) {
            readlen = subblock_size - suboffset;
        }
        rl = dufs_read_datablock_indirect(indir - 1, ptrs.pts[iref], suboffset,
                                          readlen, outbuf);
        len -= rl;
        outbuf += rl;
        iref++;
        suboffset = 0;
    }
    return tlen;
}

size_t dufs_inode_read_data(const struct inode_t *in, size_t from, size_t len,
                            u8 *buf) {
    if (len > in->fsize - from) {
        len = in->fsize - from;
    }
    size_t fullreadlen = len;
    size_t direct_bytes = INODE_REF_COUNT * DATABLOCK_SIZE;

    size_t dirblock = from / DATABLOCK_SIZE;
    size_t dirblock_off = from % DATABLOCK_SIZE;
    size_t rl;
    while (len > 0 && from < direct_bytes) {
        rl = dufs_read_datablock(in->data[dirblock], dirblock_off, len, buf);
        dirblock_off = 0;
        dirblock++;
        len -= rl;
        buf += rl;
        from += rl;
    }
    if (len == 0)
        return fullreadlen;

    from -= direct_bytes;

    for (size_t i = 0; i < INODE_INDIR_COUNT && len > 0; i++) {
        rl = dufs_read_datablock_indirect(i + 1, in->data_indir[i], from, len,
                                          buf);
        buf += rl;
        from += rl;
        len -= rl;
    }
    return fullreadlen;
}

size_t dufs_write_datablock(size_t dblock, size_t offset, size_t len,
                            const u8 *buf) {
    if (offset >= DATABLOCK_SIZE)
        return 0;

    size_t sector = dblock * SECTORS_PER_DATABLOCK;
    if (len > DATABLOCK_SIZE - offset) {
        len = DATABLOCK_SIZE - offset;
    }
    size_t roff = 0;
    for (size_t i = 0; i < SECTORS_PER_DATABLOCK && roff < len; i++) {
        size_t sector_start = i * SECTOR_SIZE;
        if (offset + roff >= sector_start &&
            offset + roff <= sector_start + SECTOR_SIZE) {
            u8 tbuf[SECTOR_SIZE];
            size_t local_off = offset + roff - sector_start;
            size_t local_len = SECTOR_SIZE - local_off;
            if (local_len > len - roff)
                local_len = len - roff;
            if (local_off > 0 || local_len < SECTOR_SIZE)
                hdd_read(sector + i, tbuf);
            memcpy(tbuf + local_off, buf + roff, local_len);
            roff += local_len;
            hdd_write(sector + i, tbuf);
        }
    }
    return roff;
}

size_t dufs_write_datablock_indirect(int indir, size_t dblock_indir,
                                     size_t offset, size_t len, const u8 *buf) {
    if (indir == 0) {
        return dufs_write_datablock(dblock_indir, offset, len, buf);
    }

    struct datablock_indir_t ptrs;
    dufs_read_datablock(dblock_indir, 0, DATABLOCK_SIZE, (u8 *)&ptrs);

    size_t subblock_size = DATABLOCK_SIZE;
    for (int i = 0; i < indir - 1; i++) {
        subblock_size *= DATABLOCK_INDIR_PTR_COUNT;
    }
    size_t my_size = subblock_size * DATABLOCK_INDIR_PTR_COUNT;
    if (offset >= my_size)
        return 0;
    if (len > my_size - offset) {
        len = my_size - offset;
    }
    size_t tlen = len;

    int iref = offset / subblock_size;
    size_t suboffset = offset % subblock_size;

    size_t wl;
    size_t prev = 0;
    while (len > 0) {
        size_t sublen = len;
        if (sublen > subblock_size - suboffset) {
            sublen = subblock_size - suboffset;
        }
        if (!DPTR_VALID(ptrs.pts[iref])) {
            blockptr_t alloc = dufs_alloc_datablock(prev + 1);
            if (alloc < 0) {
                // TODO no idea if this works
                return tlen - len;
            }
            ptrs.pts[iref] = alloc;
        }
        wl = dufs_write_datablock_indirect(indir - 1, ptrs.pts[iref], suboffset,
                                           sublen, buf);
        len -= wl;
        buf += wl;
        prev = ptrs.pts[iref];
        iref++;
        suboffset = 0;
    }
    dufs_write_datablock(dblock_indir, 0, DATABLOCK_SIZE, (u8 *)&ptrs);
    return tlen;
}

size_t dufs_inode_write_data(struct inode_t *in, size_t from, size_t len,
                             const u8 *buf) {
    size_t tlen = len;
    size_t tfrom = from;
    size_t ret;
    size_t direct_bytes = INODE_REF_COUNT * DATABLOCK_SIZE;
    bool inode_modified = false;
    size_t dirblock = from / DATABLOCK_SIZE;
    size_t dirblock_off = from % DATABLOCK_SIZE;
    size_t wl, prev = 0;
    while (len > 0 && from < direct_bytes) {
        if (!DPTR_VALID(in->data[dirblock])) {
            blockptr_t alloc = dufs_alloc_datablock(prev);
            if (alloc < 0) {
                // TODO check
                ret = tlen - len;
                goto ret;
            }
            in->data[dirblock] = alloc;
            inode_modified = true;
        }

        wl = dufs_write_datablock(in->data[dirblock], dirblock_off, len, buf);
        dirblock_off = 0;
        dirblock++;
        len -= wl;
        buf += wl;
        from += wl;
        prev = in->data[dirblock];
    }
    if (len == 0) {
        ret = tlen;
        goto ret;
    }

    from -= direct_bytes;

    for (size_t i = 0; i < INODE_INDIR_COUNT && len > 0; i++) {
        if (!DPTR_VALID(in->data_indir[i])) {
            blockptr_t alloc = dufs_alloc_datablock(prev);
            if (alloc < 0) {
                // TODO check
                ret = tlen - len;
                goto ret;
            }
            in->data_indir[i] = alloc;
            inode_modified = true;
        }
        wl = dufs_write_datablock_indirect(i + 1, in->data_indir[i], from, len,
                                           buf);
        buf += wl;
        from += wl;
        len -= wl;
        prev = in->data_indir[i];
    }

    ret = tlen;

ret:
    if (tfrom + ret > in->fsize) {
        in->fsize = tfrom + ret;
        inode_modified = true;
    }
    if (inode_modified) {
        dufs_write_inode(in, in->num);
    }
    return ret;
}

inodeptr_t dufs_dir_find_filename(const struct inode_t *dir,
                                  const char *filename, size_t *endoff) {
    assert(dir->type == INODE_TYPE_DIR);
    if (dir->fsize == 0) {
        *endoff = 0;
        return FAIL;
    }
    inodeptr_t ret;
    // ideally we would not allocate and just process the structure in chunks.
    // one only has so much time though.
    u8 *dirdata = malloc(dir->fsize);

    if (!dirdata) {
        perror("malloc");
        exit(1);
    }

    dufs_inode_read_data(dir, 0, dir->fsize, dirdata);
    size_t off = 0;

    struct direntry_t *entr;

    while (off < dir->fsize) {
        entr = (struct direntry_t *)(dirdata + off);

        if (entr->entry_size == 0) {
            goto fail;
        }
        off += entr->entry_size;

        if (!strcmp(entr->filename, filename)) { // TODO strncmp would be better
            ret = entr->inode;
            goto ret;
        }
    }

fail:
    ret = FAIL;
ret:
    free(dirdata);
    if (endoff != NULL && ret == FAIL) {
        *endoff = off;
    }
    return ret;
}

void dufs_dir_append_filename(struct inode_t *dir, const char *filename,
                              inodeptr_t target, size_t endoff) {
    assert(dir->type == INODE_TYPE_DIR);
    // this assumes that the filename does not already exist in the directory.

    u8 buf[MAX_FILENAME_LEN + 1 + sizeof(struct direntry_t)];
    struct direntry_t *entr = (struct direntry_t *)buf;
    size_t namelen = strlen(filename) + 1;
    size_t len = namelen + sizeof(struct direntry_t);

    entr->inode = target;
    entr->entry_size = len;
    strncpy(entr->filename, filename, MAX_FILENAME_LEN);

    dufs_inode_write_data(dir, endoff, entr->entry_size, buf);
    // TODO handle incomplete write
}

int dufs_dir_remove_filename(struct inode_t *dir, const char *filename) {
    int ret;
    assert(dir->type == INODE_TYPE_DIR);
    if (dir->fsize == 0)
        return FAIL;
    u8 *dirdata = malloc(dir->fsize);

    if (!dirdata) {
        perror("malloc");
        exit(1);
    }

    dufs_inode_read_data(dir, 0, dir->fsize, dirdata);

    size_t off = 0;
    bool found = false;
    struct direntry_t *entr;

    while (off < dir->fsize) {
        entr = (struct direntry_t *)(dirdata + off);

        if (entr->entry_size == 0) {
            goto fail;
        }

        if (!strcmp(entr->filename, filename)) { // TODO strncmp would be better
            found = true;
            break;
        }

        off += entr->entry_size;
    }
    if (!found) {
        goto fail;
    }
    size_t sz = entr->entry_size;
    fprintf(stderr, "dirremove: found entry. offset: %lu, size: %lu\n", off,
            sz);
    memmove(dirdata + off, dirdata + off + sz, dir->fsize - off - sz);
    memset(dirdata + dir->fsize - sz, 0, sz);

    dufs_inode_write_data(dir, 0, dir->fsize, dirdata);

    // dufs_write_inode(dir, dir->num);
    ret = OK;
    goto ret;

fail:
    ret = FAIL;
ret:
    free(dirdata);
    return ret;
}

static char dufs_tok_delim[2] = {PATHSEP, 0};
inodeptr_t dufs_path_lookup(const char *path) {
    inodeptr_t rootinode = dufs_root_inode_pos();
    if (path[0] == 0) {
        return rootinode;
    }
    assert(path[0] == PATHSEP);
    if (path[1] == 0) {
        return rootinode;
    }
    assert(strlen(path) < MAX_PATH_LEN);

    char pathcpy[MAX_PATH_LEN];
    strncpy(pathcpy, path, MAX_PATH_LEN);
    char *pathptr = pathcpy;
    pathptr++;

    struct inode_t inode;
    dufs_read_inode(&inode, rootinode);

    inodeptr_t nextptr;
    char *saveptr = NULL;
    char *ptok = strtok_r(pathptr, dufs_tok_delim, &saveptr);
    fprintf(stderr, "p: <%s>\n", ptok);

    nextptr = dufs_dir_find_filename(&inode, ptok, NULL);
    if (nextptr == FAIL) {
        return FAIL;
    }
    char *tok = strtok_r(NULL, dufs_tok_delim, &saveptr);

    while (tok != NULL) {
        fprintf(stderr, "t: <%s>\n", tok);
        dufs_read_inode(&inode, nextptr);
        if (inode.type != INODE_TYPE_DIR) { // TODO symlinks
            return FAIL;
        }
        nextptr = dufs_dir_find_filename(&inode, tok, NULL);
        if (nextptr == FAIL) {
            return FAIL;
        }
        ptok = tok;
        tok = strtok_r(NULL, dufs_tok_delim, &saveptr);
    }

    return nextptr;
}

void dufs_free_datablock_indir(int indir, size_t dblock_indir) {
    if (indir == 0) {
        dufs_bitmap_set_datablock(dblock_indir, false);
    }

    struct datablock_indir_t ptrs;
    dufs_read_datablock(dblock_indir, 0, DATABLOCK_SIZE, (u8 *)&ptrs);

    for (size_t i = 0; i < DATABLOCK_INDIR_PTR_COUNT; i++) {
        if (!DPTR_VALID(ptrs.pts[i])) {
            return;
        }
        dufs_free_datablock_indir(indir - 1, ptrs.pts[i]);
    }
}

void dufs_inode_free(struct inode_t *in) {
    for (size_t i = 0; i < INODE_REF_COUNT; i++) {
        if (!DPTR_VALID(in->data[i])) {
            return;
        }
        dufs_free_datablock_indir(0, in->data[i]);
    }
    for (size_t i = 0; i < INODE_INDIR_COUNT; i++) {
        dufs_free_datablock_indir(i + 1, in->data_indir[i]);
    }
    dufs_bitmap_set(in->num, false);
}

file_t *dufs_open_inode(inodeptr_t ino) {
    file_t *fd = fd_alloc();
    fd->info[FILET_INODEPTR] = ino;
    fd->info[FILET_OFFSET] = 0;
    return fd;
}

void dufs_close_filet(file_t *fd) { fd_free(fd); }

/**
 * Naformatovanie disku.
 *
 * Zavola sa vzdy, ked sa vytvara novy obraz disku.
 */
void fs_format() {
    struct superblock_t sb;
    size_t rootpos = dufs_root_inode_pos();
    sb.last_inode_ptr = rootpos;
    dufs_write_superblock(&sb);

    struct inode_t root;
    memset(&root, 0, sizeof(struct inode_t));
    root.type = INODE_TYPE_DIR;
    root.refcnt = 1;
    root.fsize = 0;
    root.num = rootpos;
    dufs_write_inode(&root, rootpos);
    dufs_bitmap_init();
}

/**
 * Vytvorenie suboru.
 *
 * Volanie vytvori v suborovom systeme na zadanej ceste novy subor a vrati
 * handle nan. Ak subor uz existoval, bude skrateny na prazdny. Pozicia v subore
 * bude nastavena na 0ty byte. Ak adresar, v ktorom subor ma byt ulozeny,
 * neexistuje, vrati FAIL (sam nevytvara adresarovu strukturu, moze vytvarat iba
 * subory).
 */

file_t *fs_creat(const char *path) {
    char pathcpy[MAX_PATH_LEN];
    strncpy(pathcpy, path, MAX_PATH_LEN);
    char *pathptr = pathcpy;

    char *lastsep = strrchr(pathcpy, PATHSEP);
    *lastsep = 0; // pathptr now contains prefix
    char *basename = lastsep + 1;

    inodeptr_t ret = dufs_path_lookup(pathptr);
    if (ret == FAIL) {
        return NULL;
    }
    struct inode_t dirinode;
    dufs_read_inode(&dirinode, ret);

    size_t endoff;
    if (dufs_dir_find_filename(&dirinode, basename, &endoff) != FAIL) {
        // TODO existuje
        return NULL;
    }

    inodeptr_t newptr =
        dufs_alloc_inode(0); // TODO read last loc from superblock?
    if (newptr == FAIL) {
        return NULL;
    }
    struct inode_t new;
    memset(&new, 0, sizeof(struct inode_t));
    new.refcnt = 1;
    new.type = INODE_TYPE_FILE;
    new.fsize = 0;
    new.num = newptr;
    dufs_write_inode(&new, newptr);

    dufs_dir_append_filename(&dirinode, basename, newptr, endoff);

    return dufs_open_inode(newptr);
}

/**
 * Otvorenie existujuceho suboru.
 *
 * Ak zadany subor existuje, funkcia ho otvori a vrati handle nan. Pozicia v
 * subore bude nastavena na 0-ty bajt. Ak subor neexistuje, vrati FAIL.
 */
file_t *fs_open(const char *path) {
    inodeptr_t ret = dufs_path_lookup(path);
    if (ret == FAIL) {
        return NULL;
    }
    return dufs_open_inode(ret);
}

/**
 * Zatvori otvoreny file handle.
 *
 * Funkcia zatvori handle, ktory bol vytvoreny pomocou volania 'open' alebo
 * 'creat' a uvolni prostriedky, ktore su s nim spojene. V pripade akehokolvek
 * zlyhania vrati FAIL.
 */
int fs_close(file_t *fd) {
    dufs_close_filet(fd);
    return OK;
}

/**
 * Odstrani subor na ceste 'path'.
 *
 * Ak zadana cesta existuje a je to subor, odstrani subor z disku; nemeni
 * adresarovu strukturu. V pripade chyby vracia FAIL.
 */
int fs_unlink(const char *path) {
    inodeptr_t ino = dufs_path_lookup(path);
    if (ino == FAIL) {
        return FAIL;
    }

    char pathcpy[MAX_PATH_LEN];
    strncpy(pathcpy, path, MAX_PATH_LEN);
    char *dirname = pathcpy;
    char *lastsep = strrchr(pathcpy, PATHSEP);
    *lastsep = 0;
    char *basename = lastsep + 1;

    inodeptr_t inodir = dufs_path_lookup(dirname);
    struct inode_t indir;
    dufs_read_inode(&indir, inodir);
    dufs_dir_remove_filename(&indir, basename);

    struct inode_t in;
    fprintf(stderr, "fs_unlink read file inode, ino: %u\n", ino);
    dufs_read_inode(&in, ino);
    if (--in.refcnt == 0) {
        dufs_inode_free(&in);
    } else {
        dufs_write_inode(&in, in.num);
    }
    return OK;
}

/**
 * Premenuje/presunie polozku v suborovom systeme z 'oldpath' na 'newpath'.
 *
 * Po uspesnom vykonani tejto funkcie bude subor, ktory doteraz existoval na
 * 'oldpath' dostupny cez 'newpath' a 'oldpath' prestane existovat. Opat,
 * funkcia nemanipuluje s adresarovou strukturou (nevytvara nove adresare
 * z cesty newpath, okrem posledneho v pripade premenovania adresara).
 * V pripade zlyhania vracia FAIL.
 */
int fs_rename(const char *oldpath, const char *newpath) { return FAIL; }

/**
 * Nacita z aktualnej pozicie vo 'fd' do bufferu 'bytes' najviac 'size' bajtov.
 *
 * Z aktualnej pozicie v subore precita funkcia najviac 'size' bajtov; na konci
 * suboru funkcia vracia 0. Po nacitani dat zodpovedajuco upravi poziciu v
 * subore. Vrati pocet precitanych bajtov z 'bytes', alebo FAIL v pripade
 * zlyhania. Existujuci subor prepise.
 */
int fs_read(file_t *fd, uint8_t *bytes, size_t size) {
    inodeptr_t ino = fd->info[FILET_INODEPTR];
    size_t off = fd->info[FILET_OFFSET];
    struct inode_t in;
    dufs_read_inode(&in, ino);
    int ret = dufs_inode_read_data(&in, off, size, bytes);
    fd->info[FILET_OFFSET] += ret;
    return ret;
}

/**
 * Zapise do 'fd' na aktualnu poziciu 'size' bajtov z 'bytes'.
 *
 * Na aktualnu poziciu v subore zapise 'size' bajtov z 'bytes'. Ak zapis
 * presahuje hranice suboru, subor sa zvacsi; ak to nie je mozne, zapise sa
 * maximalny mozny pocet bajtov. Po zapise korektne upravi aktualnu poziciu v
 * subore a vracia pocet zapisanych bajtov z 'bytes'.
 *
 * Write existujuci obsah suboru prepisuje, nevklada dovnutra nove data.
 * Write pre poziciu tesne za koncom existujucich dat zvacsi velkost suboru.
 */

int fs_write(file_t *fd, const uint8_t *bytes, size_t size) {
    inodeptr_t ino = fd->info[FILET_INODEPTR];
    size_t off = fd->info[FILET_OFFSET];
    struct inode_t in;
    dufs_read_inode(&in, ino);
    int ret = dufs_inode_write_data(&in, off, size, bytes);
    fd->info[FILET_OFFSET] += ret;
    return ret;
}

/**
 * Zmeni aktualnu poziciu v subore na 'pos'-ty byte.
 *
 * Upravi aktualnu poziciu; ak je 'pos' mimo hranic suboru, vrati FAIL a pozicia
 * sa nezmeni, inac vracia OK.
 */

int fs_seek(file_t *fd, size_t pos) {
    inodeptr_t ino = fd->info[FILET_INODEPTR];
    struct inode_t in;
    dufs_read_inode(&in, ino);
    if (pos > in.fsize) { // TODO maybe >=
        return FAIL;
    }
    fd->info[FILET_OFFSET] = pos;
    return OK;
}

/**
 * Vrati aktualnu poziciu v subore.
 */

size_t fs_tell(file_t *fd) { return fd->info[FILET_OFFSET]; }

/**
 * Vrati informacie o 'path'.
 *
 * Funkcia vrati FAIL ak cesta neexistuje, alebo vyplni v strukture 'fs_stat'
 * polozky a vrati OK:
 *  - st_size: velkost suboru v byte-och
 *  - st_nlink: pocet hardlinkov na subor (ak neimplementujete hardlinky, tak 1)
 *  - st_type: hodnota podla makier v hlavickovom subore: STAT_TYPE_FILE,
 *  STAT_TYPE_DIR, STAT_TYPE_SYMLINK
 *
 */

int fs_stat(const char *path, struct fs_stat *fs_stat) {
    inodeptr_t ino = dufs_path_lookup(path);
    if (ino == FAIL)
        return FAIL;

    struct inode_t in;
    dufs_read_inode(&in, ino);

    fs_stat->st_size = in.fsize;
    fs_stat->st_nlink = in.refcnt;
    fs_stat->st_type = in.type;
    return OK;
}

/* Level 3 */
/**
 * Vytvori adresar 'path'.
 *
 * Ak cesta, v ktorej adresar ma byt, neexistuje, vrati FAIL (vytvara najviac
 * jeden adresar), pri korektnom vytvoreni OK.
 */
int fs_mkdir(const char *path) { return FAIL; }

/**
 * Odstrani adresar 'path'.
 *
 * Odstrani adresar, na ktory ukazuje 'path'; ak neexistuje alebo nie je
 * adresar, vrati FAIL; po uspesnom dokonceni vrati OK.
 */
int fs_rmdir(const char *path) { return FAIL; }

/**
 * Otvori adresar 'path' (na citanie poloziek)
 *
 * Vrati handle na otvoreny adresar s poziciou nastavenou na 0; alebo FAIL v
 * pripade zlyhania.
 */
file_t *fs_opendir(const char *path) { return (file_t *)FAIL; }

/**
 * Nacita nazov dalsej polozky z adresara.
 *
 * Do dodaneho buffera ulozi nazov polozky v adresari, posunie aktualnu
 * poziciu na dalsiu polozku a vrati OK.
 * V pripade problemu, alebo ak nasledujuca polozka neexistuje, vracia FAIL.
 * (V pripade jedneho suboru v adresari vracia FAIL az pri druhom volani.)
 */
int fs_readdir(file_t *dir, char *item) { return FAIL; }

/**
 * Zatvori otvoreny adresar.
 */
int fs_closedir(file_t *dir) { return FAIL; }

/* Level 4 */
/**
 * Vytvori hardlink zo suboru 'path' na 'linkpath'.
 */
int fs_link(const char *path, const char *linkpath) { return FAIL; }

/**
 * Vytvori symlink z 'path' na 'linkpath'.
 */
int fs_symlink(const char *path, const char *linkpath) { return FAIL; }
