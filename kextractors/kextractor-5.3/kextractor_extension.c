#include <Python.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <malloc.h>

int main(int, char **);

struct module_state {
  PyObject *ExtractorError;
};

#if PY_MAJOR_VERSION >= 3
#define GETSTATE(m) ((struct module_state*)PyModule_GetState(m))
#else
#define GETSTATE(m) (&_state)
static struct module_state _state;
#define PyBytes_AsString PyString_AsString  // changed name in python 3
#endif

static PyObject * kextract(PyObject *self, PyObject *args) {
  PyObject *list_arg;
  Py_ssize_t list_size;
  char **cargs;
  int num_args;
  int cargs_idx;

  if (!PyArg_ParseTuple(args, "O", &list_arg)) {
    return NULL;
  }

  if (! PyList_Check(list_arg)) {
    PyErr_SetString(PyExc_TypeError,"Non-numeric argument.");
    return NULL;
  }

  list_size = PyList_Size(list_arg);
  num_args = list_size + 1;  // add one for the argv[0] to main of kextractor
  cargs = malloc(num_args * sizeof(char *));

  cargs_idx = 0;
  cargs[cargs_idx] = "kextractor";
  cargs_idx++;

  for (Py_ssize_t elem_idx = 0; elem_idx < list_size; elem_idx++) {
    PyObject *elem_object = PyList_GetItem(list_arg, elem_idx);
    PyObject* str = PyUnicode_AsEncodedString(elem_object, "utf-8", "~E~");
    if (PyBytes_Check(str)) {
      char *elem_string = PyBytes_AsString(str);  // will throw type error if not string
      cargs[cargs_idx] = elem_string;
      cargs_idx++;
    } else {
      return Py_BuildValue("i", 1); // return non-zero error code
    }
  }
  
  int errcode = main(num_args, cargs);

  return Py_BuildValue("i", errcode);
}

static char kextract_docs[] =
  "kextract( ): Extract Kconfig dependencies\n";

static PyMethodDef kextractor_5_3_funcs[] = {
  {"kextract", (PyCFunction)kextract, METH_VARARGS, kextract_docs},
  {NULL}
};

#if PY_MAJOR_VERSION >= 3

static int kextractor_5_3_traverse(PyObject *m, visitproc visit, void *arg) {
    Py_VISIT(GETSTATE(m)->ExtractorError);
    return 0;
}

static int kextractor_5_3_clear(PyObject *m) {
    Py_CLEAR(GETSTATE(m)->ExtractorError);
    return 0;
}


static struct PyModuleDef kextractor_5_3def = {
        PyModuleDef_HEAD_INIT,
        "kextractor_5_3",
        NULL,
        sizeof(struct module_state),
        kextractor_5_3_funcs,
        NULL,
        kextractor_5_3_traverse,
        kextractor_5_3_clear,
        NULL
};

#define INITERROR return NULL

PyMODINIT_FUNC
PyInit_kextractor_5_3(void)

#else
#define INITERROR return

void initkextractor_5_3(void)
#endif
{
#if PY_MAJOR_VERSION >= 3
    PyObject *module = PyModule_Create(&kextractor_5_3def);
#else
    PyObject *module = Py_InitModule3("kextractor_5_3", kextractor_next_20210426_funcs,
                                      "Extract Kconfig dependencies.");
#endif

  if (module == NULL)
    INITERROR;
  struct module_state *st = GETSTATE(module);
  
  st->ExtractorError = PyErr_NewException("kextractor_5_3.error", NULL, NULL);
  if (st->ExtractorError == NULL) {
      Py_DECREF(module);
      INITERROR;
  }
  Py_INCREF(st->ExtractorError);
  PyModule_AddObject(module, "error", st->ExtractorError);

#if PY_MAJOR_VERSION >= 3
    return module;
#endif
}
