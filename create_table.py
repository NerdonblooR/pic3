import boto3

dynamodb = boto3.resource('dynamodb')

table = dynamodb.create_table(
    TableName='ic3state',
    KeySchema=[
        {
            'AttributeName': 'task_id',
            'KeyType': 'HASH'  # Partition key
        },
        {
            'AttributeName': 'lemma_id',
            'KeyType': 'RANGE'  # Sort key
        }
    ],
    AttributeDefinitions=[
        {
            'AttributeName': 'task_id',
            'AttributeType': 'N'
        },
        {
            'AttributeName': 'lemma_id',
            'AttributeType': 'S'
        },

    ],
    ProvisionedThroughput={
        'ReadCapacityUnits': 20,
        'WriteCapacityUnits': 20
    }
)

print("Table status:", table.table_status)

table = dynamodb.create_table(
    TableName='ic3lemmadb',
    KeySchema=[
        {
            'AttributeName': 'lemma_id',
            'KeyType': 'HASH'  # Partition key
        },
        {
            'AttributeName': 'time_stamp',
            'KeyType': 'RANGE'  # Sort key
        }
    ],
    AttributeDefinitions=[
        {
            'AttributeName': 'lemma_id',
            'AttributeType': 'S'
        },
        {
            'AttributeName': 'time_stamp',
            'AttributeType': 'N'
        },

    ],
    ProvisionedThroughput={
        'ReadCapacityUnits': 20,
        'WriteCapacityUnits': 20
    }
)
