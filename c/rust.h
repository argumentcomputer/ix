#ifndef RUST_H
#define RUST_H

void  rs_constraint_system_free(void*);
void *rs_constraint_system_builder_build(void*);

void *rs_constraint_system_builder_init();
void  rs_constraint_system_builder_free(void*);
size_t rs_constraint_system_builder_add_channel(void*);

#endif
