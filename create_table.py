import boto3
import time

dynamodb = boto3.resource('dynamodb')


try:
    state = dynamodb.Table('ic3state')
    lemma = dynamodb.Table('ic3lemmadb')
    state.delete()
    lemma.delete()
    time.sleep(5)
except Exception as exc:
    print exc

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
        'ReadCapacityUnits': 100,
        'WriteCapacityUnits': 100
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
        'ReadCapacityUnits': 100,
        'WriteCapacityUnits': 100
    }
)
