#[macro_use]
extern crate enum_num_match;

pub mod ffi;

use std::{
    alloc::{alloc, dealloc, realloc, Layout},
    cell::Cell,
    convert::TryFrom,
    error::Error as StdErrorT,
    ffi::CStr,
    fmt::{self, Display as StdDisplayT},
    io::Read as StdReadT,
    mem::{self, MaybeUninit},
    os::raw::{c_char, c_int, c_void},
    ptr,
    rc::Rc,
    slice,
};

///////////////////////////////////////////////////////////////////////////////
// Enumerators.
///////////////////////////////////////////////////////////////////////////////

/// Error struct returned by lua.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Ok,
    Yield,
    Run,
    Err,
    File,
    Mem,
}

#[rustfmt::skip]
enum_num_match! {
    Error => c_int {
        Ok    => ffi::LUA_OK,
        Yield => ffi::LUA_YIELD,
        Run   => ffi::LUA_ERRRUN,
        Err   => ffi::LUA_ERRERR,
        File  => ffi::LUA_ERRFILE,
        Mem   => ffi::LUA_ERRMEM,
    }
}

impl StdDisplayT for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[rustfmt::skip]
        let ret = f.write_str(match *self {
            Self::Ok    => "success",
            Self::Yield => "thread yield",
            Self::Run   => "runtime error",
            Self::Err   => "error when running the error handler",
            Self::File  => "file error",
            Self::Mem   => "memory error",
        });
        ret
    }
}

impl StdErrorT for Error {}

/// Types
pub enum Type {
    None,
    Nil,
    Bool,
    LightUserdata,
    Number,
    String,
    Table,
    Function,
    Userdata,
    Thread,
}

#[rustfmt::skip]
enum_num_match! {
    Type => c_int {
        None          => ffi::LUA_TNONE,
        Nil           => ffi::LUA_TNIL,
        Bool          => ffi::LUA_TBOOLEAN,
        LightUserdata => ffi::LUA_TLIGHTUSERDATA,
        Number        => ffi::LUA_TNUMBER,
        String        => ffi::LUA_TSTRING,
        Table         => ffi::LUA_TTABLE,
        Function      => ffi::LUA_TFUNCTION,
        Userdata      => ffi::LUA_TUSERDATA,
        Thread        => ffi::LUA_TTHREAD,
    }
}

///////////////////////////////////////////////////////////////////////////////
// Constants.
///////////////////////////////////////////////////////////////////////////////

/// Lua global index.
pub const GLOBAL_INDEX: c_int = ffi::LUA_GLOBALSINDEX;

/// Lua environment index.
pub const ENVIRONMENT_INDEX: c_int = ffi::LUA_ENVIRONINDEX;

///////////////////////////////////////////////////////////////////////////////
// Main structs and traits.
///////////////////////////////////////////////////////////////////////////////

/// A valid State pointer represents a stack.
#[derive(Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Stack {
    ptr: *mut ffi::lua_State,
}

// The following lines should be uncommented immediately as soon as pointers
// become Send and Sync.
// impl !Sync for ThreadRaw {}
// impl !Send for ThreadRaw {}

impl Stack {
    /// Wrap a new instance.
    ///
    /// # Safety
    ///
    /// The inner pointer must be a valid lua_State pointer.
    #[inline]
    unsafe fn wrap(inner: *mut ffi::lua_State) -> Self {
        Self { ptr: inner }
    }

    /// Get the inner pointer.
    #[inline]
    fn ptr(&self) -> *mut ffi::lua_State {
        self.ptr
    }
}

impl StackT for Stack {
    #[inline]
    fn raw(&self) -> &Stack {
        self
    }
}

/// Lua stack trait.
pub trait StackT {
    /// Return the ThreadRaw reference.
    fn raw(&self) -> &Stack;

    /// Call a function
    #[inline]
    fn call(&self, nargs: c_int, nresults: c_int) {
        unsafe { ffi::lua_call(self.raw().ptr(), nargs, nresults) }
    }

    /// Check stack.
    #[inline]
    fn check_stack(&self, extra: c_int) -> Result<(), Error> {
        match unsafe { ffi::lua_checkstack(self.raw().ptr(), extra) } {
            0 => Ok(()),
            e => Err(Error::try_from(e)
                .expect("unknown output from lua_checkstack")),
        }
    }

    /// Create a table.
    #[inline]
    fn create_table(&self, narr: c_int, nrec: c_int) {
        unsafe { ffi::lua_createtable(self.raw().ptr(), narr, nrec) }
    }

    /// Generate error.
    #[inline]
    fn error(&self) -> Result<(), Error> {
        match unsafe { ffi::lua_error(self.raw().ptr()) } {
            0 => Ok(()),
            e => {
                Err(Error::try_from(e).expect("unknown output from lua_error"))
            }
        }
    }

    /// Generate error from string slice.
    #[inline]
    fn error_str(&self, e: &str) -> Result<(), Error> {
        self.check_stack(1)?;
        self.push_str(e);
        self.error()
    }

    /// Get field.
    #[inline]
    fn get_field(&self, index: c_int, key: &str) -> Result<(), Error> {
        self.check_stack(1)?;
        self.push_str(key);
        self.get_table(index);
        Ok(())
    }

    /// Push the metatable of the given index onto the stack if it has one, and
    /// return true; otherwise do nothing and return false.
    #[inline]
    fn get_metatable(&self, index: c_int) -> bool {
        if unsafe { ffi::lua_getmetatable(self.raw().ptr(), index) } == 0 {
            false
        } else {
            true
        }
    }

    /// Return the index of the top element.
    #[inline]
    fn get_top(&self) -> c_int {
        unsafe { ffi::lua_gettop(self.raw().ptr()) }
    }

    /// Get table.
    #[inline]
    fn get_table(&self, index: c_int) {
        unsafe { ffi::lua_gettable(self.raw().ptr(), index) }
    }

    /// Get type.
    #[inline]
    fn get_type(&self, index: c_int) -> Type {
        Type::try_from(unsafe { ffi::lua_type(self.raw().ptr(), index) })
            .expect("unknown output from lua_type")
    }

    /// Move the top element to the index. Cannot be used with pseudo-indices.
    #[inline]
    fn insert(&self, index: c_int) {
        unsafe { ffi::lua_insert(self.raw().ptr(), index) }
    }

    /// Load a readable type.
    #[inline]
    fn load<'a, R: StdReadT>(
        &self,
        reader: &'a mut R,
        chunk_name: &CStr,
        buffer_size: usize,
    ) -> Result<(), Error> {
        /// Data used by lua_reader.
        struct LuaReaderData<'a, R: StdReadT> {
            reader: &'a mut R,
            buffer_size: usize,
            buffer: *mut c_char,
        }

        // Useless but no reason why it's not Send + Sync.
        unsafe impl<'a, R: Send + StdReadT> Send for LuaReaderData<'a, R> {}
        unsafe impl<'a, R: Sync + StdReadT> Sync for LuaReaderData<'a, R> {}

        impl<'a, R: StdReadT> LuaReaderData<'a, R> {
            /// Get a layout from buffer size. May panick.
            #[inline]
            pub fn layout(buffer_size: usize) -> Layout {
                Layout::array::<c_char>(buffer_size)
                    .expect("Layout::array failed")
            }

            /// Create a new instance.
            #[inline]
            pub fn new(reader: &'a mut R, buffer_size: usize) -> Self {
                Self {
                    buffer: if buffer_size == 0 {
                        unsafe { alloc(Self::layout(buffer_size)) }.cast()
                    } else {
                        unsafe { MaybeUninit::uninit().assume_init() }
                    },
                    buffer_size,
                    reader,
                }
            }
        }

        impl<'a, R: StdReadT> Drop for LuaReaderData<'a, R> {
            #[inline]
            fn drop(&mut self) {
                if self.buffer_size != 0 {
                    unsafe {
                        dealloc(
                            self.buffer.cast(),
                            Self::layout(self.buffer_size),
                        )
                    }
                }
            }
        }

        /// Universal lua reader.
        #[inline(never)]
        unsafe extern "C" fn lua_reader<'a, R: 'a + StdReadT>(
            state: *mut ffi::lua_State,
            data: *mut c_void,
            size: *mut usize,
        ) -> *const c_char {
            let thread = Stack::wrap(state);
            let size = &mut *size.cast::<MaybeUninit<usize>>();
            let data = &mut *data.cast::<LuaReaderData<'a, R>>();

            if data.buffer_size == 0 {
                size.write(0);
            } else {
                match data.reader.read(slice::from_raw_parts_mut(
                    data.buffer.cast(),
                    data.buffer_size,
                )) {
                    Ok(s) => {
                        size.write(s);
                    }
                    Err(e) => {
                        thread
                            .error_str(&format!("{}", e))
                            .expect("State::error_str failed");
                    }
                }
            }
            data.buffer
        }

        // Real code starts here.
        let data = Cell::new(LuaReaderData::new(reader, buffer_size));
        match unsafe {
            ffi::lua_load(
                self.raw().ptr(),
                Some(lua_reader::<'a, R>),
                data.as_ptr().cast(),
                chunk_name.as_ptr(),
            )
        } {
            0 => {
                drop(data);
                Ok(())
            }
            e => {
                Err(Error::try_from(e).expect("unknwon output from lua_load"))
            }
        }
    }

    /// Create a new table.
    #[inline]
    fn new_table(&self) {
        self.create_table(0, 0)
    }

    /// Create a new thread from an Rc.
    #[inline]
    fn new_thread_with<T: Sized + StackT>(rc: &Rc<T>) -> Thread<T> {
        unsafe {
            Thread::wrap(
                rc.clone(),
                Stack::wrap(ffi::lua_newthread(rc.raw().ptr())),
            )
        }
    }

    /// Create a new full userdata. Note that the memory will be leaked without
    /// setting metamethods.
    #[inline]
    fn new_userdata<T: Sized>(&self, t: T) {
        unsafe {
            let ptr: *mut MaybeUninit<T> =
                ffi::lua_newuserdata(self.raw().ptr(), mem::size_of::<T>())
                    .cast();
            (&mut *ptr).write(t);
        }
    }

    /// Create a new full userdata with __gc metamethod implemented. The
    /// metatable of the userdata is a new table with only __gc field set.
    #[inline]
    fn new_userdata_drop<T: Sized>(&self, t: T) -> Result<(), Error> {
        /// Universal lua __gc metamethod.
        #[inline(never)]
        extern "C" fn lua_gc<T: Sized>(thread: Stack) -> c_int {
            unsafe { ptr::drop_in_place(thread.to_userdata(1).cast::<T>()) }
            0
        }
        self.new_userdata(t);
        self.check_stack(3)?;
        self.new_table();
        self.push_str("__gc");
        self.push_c_function(lua_gc::<T>);
        self.set_table(-3);
        self.set_metatable(-2);
        Ok(())
    }

    /// Protected call.
    #[inline]
    fn pcall(
        &self,
        nargs: c_int,
        nresults: c_int,
        errfunc: c_int,
    ) -> Result<(), Error> {
        match unsafe {
            ffi::lua_pcall(self.raw().ptr(), nargs, nresults, errfunc)
        } {
            0 => Ok(()),
            e => {
                Err(Error::try_from(e).expect("unknown output from lua_pcall"))
            }
        }
    }

    /// Push a boolean value.
    #[inline]
    fn push_bool(&self, b: bool) {
        unsafe {
            ffi::lua_pushboolean(self.raw().ptr(), if b { 1 } else { 0 })
        }
    }

    /// Push a c closure.
    #[inline]
    fn push_c_closure(
        &self,
        f: extern "C" fn(state: Stack) -> c_int,
        upvalue_count: c_int,
    ) {
        extern "C" {
            /// Alternative ffi::lua_pushcclosure function.
            fn lua_pushcclosure(
                state: *mut ffi::lua_State,
                f: extern "C" fn(Stack) -> c_int,
                upvalue_count: c_int,
            );
        }

        unsafe { lua_pushcclosure(self.raw().ptr(), f, upvalue_count) }
    }

    /// Push a c function.
    #[inline]
    fn push_c_function(&self, f: extern "C" fn(state: Stack) -> c_int) {
        self.push_c_closure(f, 0)
    }

    /// Push an integer.
    #[inline]
    fn push_integer(&self, n: ffi::lua_Integer) {
        unsafe { ffi::lua_pushinteger(self.raw().ptr(), n) }
    }

    /// Push light userdata (a pointer) onto the stack.
    #[inline]
    fn push_light_userdata(&self, ptr: *mut c_void) {
        unsafe { ffi::lua_pushlightuserdata(self.raw().ptr(), ptr) }
    }

    /// Push nil.
    #[inline]
    fn push_nil(&self) {
        unsafe { ffi::lua_pushnil(self.raw().ptr()) }
    }

    /// Push a number.
    #[inline]
    fn push_number(&self, n: ffi::lua_Number) {
        unsafe { ffi::lua_pushnumber(self.raw().ptr(), n) }
    }

    /// Push a slice as string.
    #[inline]
    fn push_slice(&self, s: &[u8]) {
        unsafe {
            ffi::lua_pushlstring(self.raw().ptr(), s.as_ptr().cast(), s.len())
        }
    }

    /// Push a string slice.
    #[inline]
    fn push_str(&self, s: &str) {
        unsafe {
            ffi::lua_pushlstring(self.raw().ptr(), s.as_ptr().cast(), s.len())
        }
    }

    /// Pop a table and set it as the metatable of the given index.
    #[inline]
    fn set_metatable(&self, index: c_int) {
        unsafe { ffi::lua_setmetatable(self.raw().ptr(), index) };
    }

    /// Set table.
    #[inline]
    fn set_table(&self, index: c_int) {
        unsafe { ffi::lua_settable(self.raw().ptr(), index) }
    }

    /// Set new top index.
    #[inline]
    fn set_top(&self, index: c_int) {
        unsafe { ffi::lua_settop(self.raw().ptr(), index) }
    }

    /// Return status.
    #[inline]
    fn status(&self) -> Error {
        Error::try_from(unsafe { ffi::lua_status(self.raw().ptr()) })
            .expect("unknown output from lua_status")
    }

    /// To boolean.
    #[inline]
    fn to_bool(&self, index: c_int) -> bool {
        if unsafe { ffi::lua_toboolean(self.raw().ptr(), index) } == 0 {
            false
        } else {
            true
        }
    }

    /// To c function.
    #[inline]
    fn to_c_function<F>(
        &self,
        index: c_int,
    ) -> Option<unsafe extern "C" fn(state: *mut ffi::lua_State) -> c_int>
    {
        unsafe { ffi::lua_tocfunction(self.raw().ptr(), index) }
    }

    /// To integer.
    #[inline]
    fn to_integer(&self, index: c_int) -> ffi::lua_Integer {
        unsafe { ffi::lua_tointeger(self.raw().ptr(), index) }
    }

    /// To number.
    #[inline]
    fn to_number(&self, index: c_int) -> ffi::lua_Number {
        unsafe { ffi::lua_tonumber(self.raw().ptr(), index) }
    }

    /// To a slice.
    #[inline]
    fn to_slice<F, D>(&self, index: c_int, f: F) -> D
    where
        F: FnOnce(&[c_char]) -> D,
    {
        let size = Cell::new(MaybeUninit::uninit());
        let ptr = unsafe {
            ffi::lua_tolstring(self.raw().ptr(), index, size.as_ptr().cast())
        };
        f(unsafe {
            slice::from_raw_parts(ptr, size.into_inner().assume_init())
        })
    }

    /// To userdata (a pointer).
    #[inline]
    fn to_userdata(&self, index: c_int) -> *mut c_void {
        unsafe { ffi::lua_touserdata(self.raw().ptr(), index) }
    }

    /// Get upvalue index.
    #[inline]
    fn upvalue_index(&self, index: c_int) -> c_int {
        GLOBAL_INDEX - index
    }
}

/// Stack with Send implemented.
#[derive(Debug, PartialEq, Eq)]
#[repr(C)]
pub struct StackSend(Stack);

impl StackSend {
    /// Wrap a new instance.
    ///
    /// # Safety
    ///
    /// This thread must be sendable.
    #[inline]
    pub unsafe fn wrap(inner: Stack) -> Self {
        Self(inner)
    }

    /// Unwrap the instance.
    #[inline]
    pub fn unwrap(self) -> Stack {
        self.0
    }
}

unsafe impl Send for StackSend {}

impl StackT for StackSend {
    #[inline]
    fn raw(&self) -> &Stack {
        &self.0
    }
}

/// Lua thread stack.
#[derive(Debug, PartialEq, Eq)]
pub struct Thread<T: StackT> {
    parent: Rc<T>,
    inner: Stack,
}

impl<T: StackT> Thread<T> {
    /// Wrap a new instance.
    ///
    /// # Safety
    ///
    /// inner must belong to state.
    #[inline]
    pub unsafe fn wrap(parent: Rc<T>, inner: Stack) -> Self {
        Self { parent, inner }
    }

    /// Get a reference of the parent stack.
    #[inline]
    pub fn parent(&self) -> &T {
        &*self.parent
    }
}

impl<T: StackT> StackT for Thread<T> {
    #[inline]
    fn raw(&self) -> &Stack {
        &self.inner
    }
}

/// Lua state struct.
#[derive(Debug, PartialEq, Eq)]
#[repr(C)]
pub struct State(StackSend);

impl State {
    /// Wrap a new instance.
    ///
    /// # Safety
    ///
    /// The thread must be the main thread returned from lua_newstate.
    #[inline]
    pub unsafe fn wrap(thread: StackSend) -> Self {
        Self(thread)
    }

    /// Create a new instance.
    #[inline]
    pub fn new() -> Result<Self, Error> {
        /// Default alignment.
        const MAX_ALIGN: usize = (usize::BITS >> 3) as usize;

        /// Function used by lua as allocator.
        unsafe extern "C" fn lua_alloc(
            data: *mut c_void,
            ptr: *mut c_void,
            osize: usize,
            nsize: usize,
        ) -> *mut c_void {
            let _data = MaybeUninit::new(data);

            if nsize == 0 {
                if osize != 0 {
                    dealloc(
                        ptr.cast(),
                        Layout::from_size_align(osize, MAX_ALIGN)
                            .expect("Layout::from_size_align failed"),
                    );
                }
                ptr::null_mut()
            } else {
                let layout = Layout::from_size_align(nsize, MAX_ALIGN)
                    .expect("Layout::from_size_align failed");
                if osize == 0 {
                    alloc(layout).cast()
                } else {
                    realloc(ptr.cast(), layout, nsize).cast()
                }
            }
        }

        // Real code starts here.
        let new_state = unsafe {
            ffi::lua_newstate(
                Some(lua_alloc),
                MaybeUninit::uninit().assume_init(),
            )
        };
        if new_state.is_null() {
            Err(Error::Mem)
        } else {
            Ok(unsafe {
                Self::wrap(StackSend::wrap(Stack::wrap(new_state)))
            })
        }
    }
}

impl Drop for State {
    #[inline]
    fn drop(&mut self) {
        unsafe { ffi::lua_close(self.0.raw().ptr()) }
    }
}

impl StackT for State {
    #[inline]
    fn raw(&self) -> &Stack {
        self.0.raw()
    }
}
