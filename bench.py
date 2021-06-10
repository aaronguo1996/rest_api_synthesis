#!/usr/bin/env python3

#####
# BENCH RUNNER SCRIPT
#
# this script runs a set of tests defined as json files (one per API) in the
# rest_api_synthesis/benchmarks/ directory (any dir can be specified; this is
# the default). in the future this script will format the results as a latex
# table for inclusion in a latex file.
#
#####

import argparse

from benchmarks.benchmark import BenchConfig, Benchmark, BenchmarkSuite, Bencher
from schemas import types
from analyzer import dynamic

bias_type_args = {
    "none": dynamic.BiasType.NONE,
    "simple": dynamic.BiasType.SIMPLE,
    "look-ahead": dynamic.BiasType.LOOK_AHEAD
}

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("output", nargs='?',
        help="Path to output latex table to")
    parser.add_argument("--repeat", type=int, nargs='?', default=5,
        help="Number of times to repeat filtering")
    parser.add_argument("--filter-num", type=int, nargs='?', default=3,
        help="Number of times to run filtering")
    parser.add_argument("--bias-type", default='simple', 
        choices=list(bias_type_args.keys()) ,dest='bias_type',
        help="Bias type for retrospective execution")
    parser.add_argument("--bench", nargs='?',
        help="Path to benchmark file or directory (by default runs all in benchmarks)")
    parser.add_argument("--names", nargs="+",
        help="Benchmark name list")
    parser.add_argument("--cache", action='store_true', dest='cache',
        help="Whether to use cached results")
    parser.set_defaults(cache=False)
    parser.add_argument("--sol-only", action='store_true', dest='filter_sol_only',
        help="Whether to run retrospective execution on the solution only")
    parser.add_argument("--synthesis-only", action='store_true',
        help="Whether to run ranking")
    parser.set_defaults(filter_sol_only=False)
    return parser


################################################################################
##                                  SLACK                                     ##
################################################################################

slack_benchmarks = [
    Benchmark(
        "1.1",
        "Retrieve all member emails from channel name",
        {
            "channel_name": types.PrimString("objs_conversation.name")
        },
        types.ArrayType(None, types.PrimString("objs_user_profile.email")),
        [[
            "\\channel_name -> {",
            "let x0 = /conversations.list_GET()",
            "x1 <- x0.channels",
            "if x1.name = channel_name",
            "let x2 = /conversations.members_GET(channel=x1.id)",
            "x3 <- x2.members",
            "let x4 = /users.profile.get_GET(user=x3)",
            "return x4.profile.email",
            "}"
        ]],
    ),
    Benchmark(
        "1.2",
        "Send a message to some user given the email address",
        {
            "email": types.PrimString("objs_user_profile.email")
        },
        types.SchemaObject("objs_message"),
        [[
            "\\email -> {",
            "let x0 = /users.lookupByEmail_GET(email=email)",
            "let x1 = /conversations.open_POST(users=x0.user.id)",
            "let x2 = /chat.postMessage_POST(channel=x1.channel.id)",
            "return x2.message",
            "}"
        ]],
    ),
    Benchmark(
        "1.3",
        "Get all unread message for a user",
        {
            "user_id": types.PrimString("defs_user_id")
        },
        types.ArrayType(None, types.ArrayType(None, types.SchemaObject("objs_message"))),
        [[
            "\\user_id -> {",
            "let x0 = /users.conversations_GET(user=user_id)",
            "x1 <- x0.channels",
            "let x2 = /conversations.info_GET(channel=x1.id)",
            "let x3 = x2.last_read",
            "let x5 = /conversations.history_GET(channel=x2.id, oldest=x3)",
            "return x5",
            "}"
        ]],
    ),
]

slack_suite = BenchmarkSuite(
    "configs/slack_config.json",
    "Slack",
    slack_benchmarks
)


################################################################################
##                                  STRIPE                                    ##
################################################################################

stripe_benchmarks = [
    Benchmark(
        "2.1",
        "Make a subscription to a product for a customer",
        {
            "customer": types.PrimString("customer.id"),
            "product": types.PrimString("product.id"),
        },
        types.SchemaObject("subscription"),
        [[
            "\\customer_id product_id -> {",
            "let x1 = /v1/prices_GET(product=product_id)",
            "x2 <- x1.data",
            "let x3 = /v1/subscriptions_POST(customer=customer_id, items[0].price=x2.id)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.2",
        "Charge a saved card given customer id",
        {
            "customer_id": types.PrimString("customer.id"),
            "cur": types.PrimString("fee.currency"),
            "amt": types.PrimInt("price.unit_amount"),
        },
        types.SchemaObject("payment_intent"),
        [[
            "\\customer_id cur amt -> {",
            "let x1 = /v1/payment_methods_GET(customer=customer_id, type=card)",
            "let x2 = /v1/payment_intents_POST(customer=customer_id, payment_method=x1.id, currency=cur, amount=amt)",
            "let x3 = /v1/payment_intents/{pi}/confirm_POST(pi=x2.id, setup_future_usage=off_session)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.3",
        "Subscribe to multiple items",
        {
            "customer_id": types.PrimString("customer.id"),
            "product_id": types.ArrayType(None, types.PrimString("product.id")),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [[
            "\\customer_id product_ids -> {",
            "x0 <- product_ids"
            "let x1 = /v1/prices_GET(product=x0)",
            "x2 <- x1.data",
            "let x3 = /v1/subscriptions_POST(customer=customer_id, items[0].price=x2.id)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.4",
        "Create a product and invoice a customer",
        {
            "product_name": types.PrimString("product.name"),
            "customer_id": types.PrimString("customer.id"),
            "currency": types.PrimString("fee.currency"),
            "unit_amount": types.PrimInt("price.unit_amount"),
        },
        types.SchemaObject("invoiceitem"),
        [[
            "\\product_name customer_id currency unit_amount -> {",
            "let x0 = /v1/products_POST(name=product_name)",
            "let x1 = /v1/prices_POST(currency=currency, product=x0.id, unit_amount=unit_amount)",
            "let x2 = /v1/invoiceitems_POST(customer=customer_id, price=x1.id)",
            "return x2",
            "}"
        ]]
    ),
    Benchmark(
        "2.5",
        "sending invoice",
        {
            "customer_id": types.PrimString("customer.id"),
            "price_id": types.PrimString("plan.id"),
        },
        types.SchemaObject("invoice"),
        [[
            "\\customer_id price_id -> {",
            "let x1 = /v1/invoiceitems_POST(customer=customer_id, price=price_id);",
            "let x2 = /v1/invoices_POST(customer=x1.customer);",
            "let x3 = /v1/invoices/{invoice}/send_POST(invoice=x2.id);",
            "return x3;",
            "}"
        ]]
    ),
    Benchmark(
        "2.6",
        "Retrieve customer by email",
        {
            "email": types.PrimString("customer.email"),
        },
        types.SchemaObject("customer"),
        [[
            "\\customer_email -> {",
            "let x0 = /v1/customers_GET()",
            "x1 <- x0.data",
            "if x1.email = customer_email",
            "return x1",
            "}"
        ]]
    ),
    Benchmark(
        "2.7",
        "Get a list of receipts for a customer",
        {
            "customer_id": types.PrimString("customer.id"),
        },
        types.ArrayType(None, types.SchemaObject("charge")),
        [[
            "\\customer_id -> {",
            "let x1 = /v1/invoices_GET(customer=customer_id)",
            "x2 <- x1.data",
            "let x3 = /v1/charges/{charge}_GET(charge=x2.charge)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.8",
        "Get refund for given subscription",
        {
            "subscription": types.PrimString("subscription.id"),
        },
        types.SchemaObject("refund"),
        [[
            "\\subscription_id -> {",
            "let x0 = /v1/subscriptions/{subscription_exposed_id}_GET(subscription_exposed_id=subscription_id)",
            "let x1 = /v1/invoices_GET(customer=x0.customer)",
            "x2 <- x1.data",
            "let x3 = /v1/refunds/{refund}_POST(refund=x2.charge)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.9",
        "Get email of all customers",
        {
        },
        types.ArrayType(None, types.PrimString("customer.email")),
        [[
            "\\ -> {",
            "let x0 = /v1/customers_GET()",
            "x1 <- x0.data",
            "return x1.email",
            "}"
        ]]
    ),
    Benchmark(
        "2.10",
        "Get email of subscribers to some product",
        {
            "product_id": types.PrimString("product.id"),
        },
        types.ArrayType(None, types.PrimString("customer.email")),
        [[
            "\\product_id -> {",
            "let x1 = /v1/subscriptions_GET()",
            "x2 <- x1",
            "if x2.items.product = product_id",
            "let x3 = /v1/customers/{customer}_GET(customer=x2.customer_id)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.11",
        "Get last 4 digit of card for a customer",
        {
            "customer_id": types.PrimString("customer.id"),
        },
        types.PrimString("bank_account.last4"),
        [[
            "\\customer_id -> {",
            "let x0 = /v1/customers/{customer}/sources_GET(customer=customer_id)",
            "x1 <- x0.data",
            "return x1.last4",
            "}"
        ]]
    ),
    Benchmark(
        "2.12",
        "Delete a card for a customer",
        {
            "payment_method": types.SchemaObject("payment_method"),
        },
        types.SchemaObject("deleted_payment_source"),
        [[
            "\\customer_id -> {",
            "let x1 = /v1/customers/{customer}_GET(customer=customer_id)",
            "let x2 = customer.default_source",
            "let x3 = /v1/customers/{customer}/sources/{source}_DELETE(customer=customer_id, source=x2)",
            "return x3",
            "}"
        ]]
    ),
    Benchmark(
        "2.13",
        "Update payment methods of a customer for all subscriptions",
        {
            "payment_method": types.SchemaObject("payment_method"),
            "customer_id": types.PrimString("customer.id"),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [[
            "(payment, customer_id) -> {",
            "x1 <- /v1/subscriptions_GET(customer=customer_id)",
            "let x2 = /v1/subscriptions/{subscription}_POST(subscription=x1.id, default_payment_method=payment)",
            "return x2",
            "}"
        ]]
    ),
]

stripe_suite = BenchmarkSuite(
    "configs/stripe_config.json",
    "Stripe",
    stripe_benchmarks
)

################################################################################
##                                  SQUARE                                    ##
################################################################################

square_benchmarks = [
    Benchmark(
        "3.1",
        "List invoices that match location id",
        {
            "location_id": types.PrimString("Location.id"),
        },
        types.ArrayType(None, types.SchemaObject("Invoice")),
        [[
            "\\location_id -> {",
                "let x0 = /v2/invoices_GET(location_id=location_id)",
                "x1 <- x0.invoices",
                "if x1.location_id = location_id",
                "return x1",
            "}"
        ]],
    ),
    Benchmark(
        "3.2",
        "Find subscription from location, customer, and plan id",
        {
            "customer_id": types.PrimString("Customer.id"),
            "location_id": types.PrimString("Location.id"),
            "subscription_plan_id": types.PrimString("CatalogObject.id"),
        },
        types.ArrayType(None, types.SchemaObject("Subscription")),
        [[
            "\\customer_id location_id subscription_plan_id -> {",
                "let x0 = /v2/subscriptions/search_POST()",
                "x1 <- x0.subscriptions",
                "if x1.customer_id = customer_id",
                "if x1.plan_id = subscription_plan_id",
                "if x1.location_id = location_id",
                "return x1",
            "}"
        ], [
            "\\customer_id location_id subscription_plan_id -> {",
            "let x0 = /v2/subscriptions/search_POST()",
            "x1 <- x0.subscriptions",
            "if x1.location_id = location_id",
            "if x1.plan_id = subscription_plan_id",
            "if x1.customer_id = customer_id",
            "return x1",
            "}"
        ]],
    ),
    Benchmark(
        "3.3",
        "Get all items tax applies to",
        {
            "tax_id": types.PrimString("CatalogObject.id"),
        },
        types.ArrayType(None, types.SchemaObject("CatalogObject")),
        [[
            "\\tax_id -> {",
            "let x0 = /v2/catalog/batch-retrieve_POST()",
            "x1 <- x0",
            "if x1.tax_id = tax_id",
            "}"
        ]],
    ),
    Benchmark(
        "3.4",
        "List discounts in catalog",
        {
        },
        types.ArrayType(None, types.PrimString("CatalogDiscount")),
        [[
            "\\ -> {",
            "let x0 = /v2/catalog/batch-retrieve_POST()",
            "x1 <- x0",
            "return x1.discount_data",
            "}"
        ]],
    ),
    Benchmark(
        "3.5",
        "Delete catalog items with [names]",
        {
            "item_type": types.PrimString("CatalogObject.type"),
            "names": types.ArrayType(None, types.PrimString("CatalogDiscount.name"))
        },
        types.ArrayType(None, types.PrimString("CatalogObject.Id")),
        [[
            "\\item_type, names -> {",
                "let x0 = names.map(name => {",
                    "let x1 = /v2/catalog/search-catalog-items_POST({",
                        "object_types: [item_type],",
                        "query: {",
                            "exact_query: {",
                                "attribute_name: \"name\",",
                                "attribute_value: name",
                                "}",
                                "}",
                                "})",
                                "x2 <- x1",
                                "./v2/catalog/batch-delete({",
                                    "object_ids: x2.id",
                                    "})",
                                    "return x1",
                                    "})",
                                    "return x0",
                                    "}"
        ]],
    ),
    Benchmark(
        "3.6",
        "Delete all catalog items",
        {
        },
        types.ArrayType(None, types.PrimString("CatalogObject.Id")),
        [[
            "\\ -> {",
            "let x0 = /v2/catalog/batch-retrieve_POST()",
            "x1 <- x0",
            "/v2/catalog/batch-delete_POST(object_ids = x1)",
            "}"
        ]],
    ),
    Benchmark(
        "3.7",
        "Add order details to order",
        {
            "location_id": types.PrimString("Location.id"),
            "order_ids": types.ArrayType(None, types.PrimString("Order.id")),
            "updates": types.SchemaObject("OrderFulfillment"),
        },
        types.ArrayType(None, types.SchemaObject("Order")),
        [[
            "\\location_id, order_ids, updates -> {",
                "let x0 = /v2/orders/batch-retrieve_POST(location_id=location_id, order_ids=order_ids)",
                "x1 <- x0",
                "let x2 = /v2/orders_POST(order_id=x1, order[fulfillments]=updates)",
                "return x2",
            "}"
        ]],
    ),
    Benchmark(
        "3.8",
        "Get payment notes",
        {
        },
        types.ArrayType(None, types.PrimString("Payment.note")),
        [[
            "\\ -> {",
            "let x0 = /v2/payments_GET()",
            "x1 <- x0.payments",
            "return x1.note",
            "}"
        ]],
    ),
    Benchmark(
        "3.9",
        "Get customer and items associated with your transactions",
        {
            "location_id": types.PrimString("Location.id"),
        },
        types.ArrayType(None, types.PrimString("Order.id")),
        [[
            "\\location_id -> {",
            "let x0 = /v2/locations/{location_id}/transactions_GET(location_id=location_id)",
            "x1 <- x0.transactions",
            "return x1.order_id",
            "}"
        ]],
    ),
    Benchmark(
        "3.10",
        "Get product details (names of orders) from transaction id",
        {
            "location_id": types.PrimString("Location.id"),
            "transaction_id": types.PrimString("Order.id"),
        },
        types.ArrayType(None, types.PrimString("Invoice.title")),
        [[
            "\\location_id transaction_id -> {",
            "let x0 = /v2/orders/batch-retrieve_POST(locationId = location_id, orderIds = [transaction_id])",
            "x1 <- x0",
            "x2 <- x1.line_items",
            "return item.name",
            "}"
        ]],
    ),
    Benchmark(
        "3.11",
        "Search customers by name",
        {
            "name": types.PrimString("Customer.given_name"),
        },
        types.SchemaObject("Customer"),
        [[
            "\\name -> {",
            "let x0 = /v2/customers_GET()",
            "x1 <- x0.customers",
            "if x1.given_name = name",
            "return x1",
            "}"
        ]],
    )
]

square_suite = BenchmarkSuite(
    "configs/square_config.json",
    "Square",
    square_benchmarks
)

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    config = BenchConfig(
        args.cache, 
        args.repeat,
        args.filter_num,
        args.filter_sol_only,
        args.synthesis_only,
        bias_type_args[args.bias_type])
    b = Bencher(
        [
            slack_suite,
            stripe_suite,
            square_suite,
        ],
        config)
    b.run(
        args.names,
        output=args.output, 
        print_api=True, 
        print_results=True, 
        cached_results=False)

if __name__ == '__main__':
    main()
