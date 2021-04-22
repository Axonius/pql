"""
This file includes Projection specific AST parsers.
Most of them are identical to regular parsers but with **kwargs in the signature.
The kwargs have 3 arguments which are used across the parser logic -
compared_field, array_fields and complex_fields.
compared_fields is the fields from the left hand of the expression.
array fields is a set of all fields of array type.
complex fields is a set of all complex fields that are being filtered.

Some of the methods, receive **kwargs but doesn't use it - it's important not to remove.
There are some generic methods which calls these method according to the AST type.
"""
import ast

from axonius.pql.matching import BaseAstHandler, BaseParser, ParseError,\
    GenericField, BaseFunc, IntFunc, ListFunc, DateTimeFunc, BaseOperator,\
    StringBaseField, IntBaseField, BoolBaseField, DictBaseField, ListBaseField,\
    BaseField


class ProjectionAstHandler(BaseAstHandler):

    def handle(self, thing, **kwargs):
        return self.resolve(thing)(thing, **kwargs)

    def parse(self, string, **kwargs):
        ex = ast.parse(string, mode='eval')
        return self.handle(ex.body, **kwargs)


class ProjectionParser(BaseParser, ProjectionAstHandler):
    def __init__(self, operator_map):
        self._operator_map = operator_map

    def handle_Call(self, op, **kwargs):
        if op.func.id != 'search':
            raise ParseError(f'Unsupported method call {op.func.id}')
        return {'$text': {'$search': f'\"{op.args[0].s}\"', '$caseSensitive': False}}

    def handle_BoolOp(self, op, **kwargs):
        def handle_op(value):
            return self.handle(value, **kwargs)

        return {self.handle(op.op, **kwargs): list(map(handle_op, op.values))}

    def handle_And(self, op, **kwargs):
        '''and'''
        return '$and'

    def handle_Or(self, op, **kwargs):
        '''or'''
        return '$or'

    def handle_UnaryOp(self, op, **kwargs):
        operator = self.handle(op.operand, **kwargs)
        field, value = list(operator.items())[0]
        return {
            self.handle(op.op): {
                field: value
            }
        }

    def handle_Compare(self, compare, **kwargs):
        if len(compare.comparators) != 1:
            raise ParseError('Invalid number of comparators: {0}'.format(len(compare.comparators)),
                             col_offset=compare.comparators[1].col_offset)
        try:
            return self._operator_map.handle(left=compare.left,
                                             operator=compare.ops[0],
                                             right=compare.comparators[0],
                                             **kwargs)
        except ParseError as err:
            if err.message.startswith('Unsupported syntax'):
                return self.handle_field_comparison(compare)
            raise


class ProjectionSchemaFreeParser(ProjectionParser):
    def __init__(self):
        super(ProjectionSchemaFreeParser, self).__init__(ProjectionSchemaFreeOperatorMap())


class FieldName(ProjectionAstHandler):
    def handle_Str(self, node):
        return node.s

    def handle_Name(self, name):
        return name.id

    def handle_Attribute(self, attr):
        return '{0}.{1}'.format(self.handle(attr.value), attr.attr)


class OperatorMap(object):
    def resolve_field(self, node):
        return FieldName().handle(node)

    def handle(self, operator, left, right):
        field = self.resolve_field(left)
        return {field: self.resolve_type(field).handle_operator_and_right(operator, right)}


class ProjectionMap(object):
    def resolve_field(self, node):
        return FieldName().handle(node)

    def handle(self, operator, left, right, compared_field=None, array_fields=None, complex_fields=None):
        field = self.resolve_field(left)
        condition = self.resolve_type(field).handle_operator_with_right_and_left(operator, right, compared_field=field,
                                                                                 array_fields=array_fields,
                                                                                 complex_fields=complex_fields)

        if (complex_fields and field in complex_fields) and (array_fields and field in array_fields):
            return {
                '$and': [
                    {
                        '$isArray': f'${field}'
                    },
                    {
                        '$anyElementTrue': {
                            '$map': {
                                'input': {
                                    '$cond': {
                                        'if': {
                                            '$isArray': f'${field}'
                                        },
                                        'then': f'${field}',
                                        'else': []
                                    }
                                },
                                'as': field.split('.')[-1],
                                'in': {
                                    '$cond': {
                                        'if': condition,
                                        'then': True,
                                        'else': False
                                    }
                                }
                            }
                        }
                    }
                ]
            }

        return condition


class SchemaFreeOperatorMap(OperatorMap):
    def get_options(self):
        return None

    def resolve_type(self, field):
        return GenericField()


class ProjectionSchemaFreeOperatorMap(ProjectionMap):
    def get_options(self):
        return None

    def resolve_type(self, field):
        return ProjectionGenericField()


class SchemaAwareOperatorMap(OperatorMap):
    def __init__(self, field_to_type):
        self._field_to_type = field_to_type

    def resolve_field(self, node):
        field = super(SchemaAwareOperatorMap, self).resolve_field(node)
        try:
            self._field_to_type[field]
        except KeyError:
            raise ParseError('Field not found: {0}.'.format(field),
                             col_offset=node.col_offset,
                             options=self._field_to_type.keys())
        return field

    def resolve_type(self, field):
        return self._field_to_type[field]


# ---Function-Handlers---#


class ProjectionFunc(BaseFunc, ProjectionAstHandler):

    @staticmethod
    def parse_arg(node, index, field, **kwargs):
        return field.handle(ProjectionFunc.get_arg(node, index), **kwargs)

    def handle(self, node, **kwargs):
        try:
            handler = getattr(self, 'handle_' + node.func.id)
        except AttributeError:
            raise ParseError('Unsupported function ({0}).'.format(node.func.id),
                             col_offset=node.col_offset,
                             options=self.get_options())
        return handler(node, **kwargs)

    def handle_exists(self, node):
        return {
            '$exists': self.parse_arg(node, 0, ProjectionBoolField())
        }


class ProjectionStringFunc(ProjectionFunc):

    def handle_regexMatch(self, node, compared_field=None, array_fields=None, complex_fields=None):
        if array_fields and compared_field in array_fields:
            field = f'$${compared_field.split(".")[-1]}'
        else:
            field = f'${compared_field}'
        result = {
            '$and': [
                {
                    '$eq': [
                        'string',
                        {
                            '$type': field
                        }
                    ]
                },
                {
                    '$regexMatch': {
                        'input': field,
                        'regex': self.parse_arg(node, 0, ProjectionStringField()),
                    }
                }
            ]
        }
        try:
            result['$and'][1]['$regexMatch']['options'] = self.parse_arg(node, 1, ProjectionStringField())
        except ParseError:
            pass
        return result


class ProjectionGenericFunc(ProjectionStringFunc, IntFunc, ListFunc, DateTimeFunc):
    pass


# ---Operators---#


class ProjectionOperator(BaseOperator, ProjectionAstHandler):

    def handle_Eq(self, node, compared_field=None, array_fields=None, complex_fields=None):
        '''=='''
        return self.field.handle(node, compared_field=compared_field, array_fields=array_fields,
                                 complex_fields=complex_fields)


class ProjectionAlgebricOperator(ProjectionOperator):
    pass


# ---Field-Types---#


class ProjectionField(BaseField, ProjectionAstHandler):
    OP_CLASS = ProjectionOperator

    def handle_Name(self, node, compared_field=None, **kwargs):
        try:
            return {
                '$eq': [f'${compared_field}', self.SPECIAL_VALUES[node.id]]
            }
        except KeyError:
            raise ParseError('Invalid name: {0}'.format(node.id), node.col_offset, options=list(self.SPECIAL_VALUES))

    def handle_operator_with_right_and_left(self, operator, right, **kwargs):
        return self.OP_CLASS(self).resolve(operator)(right, **kwargs)


class ProjectionAlgebricField(ProjectionField):
    OP_CLASS = ProjectionAlgebricOperator


class ProjectionStringField(StringBaseField, ProjectionAlgebricField):

    def handle_Str(self, node, compared_field=None, array_fields=None, complex_fields=None):
        if not compared_field:
            return node.s
        if array_fields and compared_field in array_fields:
            field = f'$${compared_field.split(".")[-1]}'
        else:
            field = f'${compared_field}'
        return {'$eq': [field, node.s]}


class ProjectionIntField(IntBaseField, ProjectionAlgebricField):
    def handle_Num(self, node, compared_field=None, array_fields=None, complex_fields=None):
        if array_fields and compared_field in array_fields:
            field = f'$${compared_field.split(".")[-1]}'
        else:
            field = f'${compared_field}'
        return {'$eq': [field, node.n]}


class ProjectionBoolField(BoolBaseField, ProjectionField):
    pass


class ProjectionListField(ListBaseField, ProjectionField):
    pass


class ProjectionDictField(DictBaseField, ProjectionField):

    def handle_Dict(self, node, **kwargs):
        return {
            '$and': [{ProjectionStringField().handle(key): (self._field or ProjectionGenericField()).handle(value)}
                     for key, value in zip(node.keys, node.values)]
        }


class ProjectionGenericField(ProjectionIntField, ProjectionBoolField, ProjectionStringField,
                             ProjectionListField, ProjectionDictField):
    def handle_Call(self, node, **kwargs):
        return ProjectionGenericFunc().handle(node, **kwargs)
